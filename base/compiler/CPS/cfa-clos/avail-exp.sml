structure AvailableExpression :> sig
  val transform : LabelledCPS.function -> LabelledCPS.function
end = struct
  structure LCPS = LabelledCPS
  structure LV = LambdaVar

  datatype select = Select of LV.lvar * int
  fun compare (Select (x, i), Select (y, j)) =
    (case LV.compare (x, y)
       of EQUAL => Int.compare (i, j)
        | order => order)

  structure Map = RedBlackMapFn(struct
    type ord_key = select
    val compare = compare
  end)

  type avail_map = LV.lvar Map.map
  type replace_map = LV.lvar LV.Map.map

  fun replaceVar (rp: replace_map) v =
    (case LV.Map.find (rp, v)
       of SOME w => w
        | NONE => v)

  fun replaceValue rp (CPS.VAR v) = CPS.VAR (replaceVar rp v)
    | replaceValue rp value = value

  fun replacePath rp (l, value, path) = (l, replaceValue rp value, path)

  datatype status = Avail of replace_map
                  | New of avail_map

  fun record (rp, av, CPS.VAR v, idx, dst) =
    (case Map.find (av, Select (v, idx))
       of SOME dst' => Avail (LV.Map.insert (rp, dst, dst'))
        | NONE => New (Map.insert (av, Select (v, idx), dst)))
    | record _ = raise Fail "select non var"

  fun transform (kind, name, args, tys, exp) =
    (kind, name, args, tys, go (LV.Map.empty, Map.empty, exp))
  and go (rp, av, exp) =
    (case exp
       of LCPS.SELECT (label, idx, arg, x, ty, exp) =>
            let val arg = replaceValue rp arg
            in  case record (rp, av, arg, idx, x)
                  of Avail rp =>
                       go (rp, av, exp)
                   | New av =>
                       LCPS.SELECT (label, idx, arg, x, ty, go (rp, av, exp))
            end
        | LCPS.RECORD (label, rk, fields, x, exp)  =>
            LCPS.RECORD
              (label, rk, map (replacePath rp) fields, x, go (rp, av, exp))
        | LCPS.OFFSET _ => raise Fail "offset"
        | LCPS.APP (label, f, args) =>
            LCPS.APP (label, replaceValue rp f, map (replaceValue rp) args)
        | LCPS.FIX (label, functions, exp) =>
            LCPS.FIX (label, map transform functions, go (rp, av, exp))
        | LCPS.SWITCH (label, arg, label2, branches) =>
            LCPS.SWITCH (label, replaceValue rp arg, label2,
                         map (fn e => go (rp, av, e)) branches)
        | LCPS.BRANCH (label, rator, args, label2, e1, e2) =>
            LCPS.BRANCH (label, rator, map (replaceValue rp) args, label2,
                         go (rp, av, e1), go (rp, av, e2))
        | LCPS.SETTER (label, rator, args, exp) =>
            LCPS.SETTER (label, rator, map (replaceValue rp) args,
                         go (rp, av, exp))
        | LCPS.LOOKER (label, rator, args, x, ty, exp) =>
            LCPS.LOOKER (label, rator, map (replaceValue rp) args, x, ty,
                         go (rp, av, exp))
        | LCPS.ARITH (label, rator, args, x, ty, exp) =>
            LCPS.ARITH (label, rator, map (replaceValue rp) args, x, ty,
                        go (rp, av, exp))
        | LCPS.PURE (label, rator, args, x, ty, exp) =>
            LCPS.PURE (label, rator, map (replaceValue rp) args, x, ty,
                       go (rp, av, exp))
        | LCPS.RCC (label, b, s, proto, args, rets, exp) =>
            LCPS.RCC (label, b, s, proto, map (replaceValue rp) args, rets,
                      go (rp, av, exp)))
end
