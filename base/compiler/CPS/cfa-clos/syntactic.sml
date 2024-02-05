structure SyntacticInfo :> sig
  type t

  val calculate : LabelledCPS.function -> t
  val typeof         : t -> LabelledCPS.lvar -> LabelledCPS.cty
  val definitionSite : t -> LabelledCPS.lvar -> LabelledCPS.function
  val useSites       : t -> LabelledCPS.lvar -> LabelledCPS.FunSet.set
  val binderOf       : t -> LabelledCPS.function -> LabelledCPS.function option
  val fv             : t -> LabelledCPS.function -> LambdaVar.Set.set
  val dump : t -> unit
end = struct
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar

  type var_info = { ty: LCPS.cty, def: LCPS.function, uses: LCPS.FunSet.set }
  type fun_info = { binder: LCPS.function option, fv: LV.Set.set }

  datatype t = T of {
    funTbl: fun_info LCPS.FunTbl.hash_table,
    varTbl: var_info LV.Tbl.hash_table,
    lam0: LCPS.function
  }

  fun kindToCty (CPS.CONT | CPS.KNOWN_CONT) = CPS.CNTt
    | kindToCty _ = CPS.FUNt

  val add = LV.Set.add
  val subtract = LV.Set.subtract
  fun subtracts (set, xs) = foldr LV.Set.subtract' set xs
  fun addV (m, CPS.VAR v) = add (m, v)
    | addV (m, _) = m
  fun addVs (m, vs) = foldr (fn (v, m) => addV (m, v)) m vs

  exception SyntacticInfo
  fun calculate (cps: LCPS.function) : t =
    let
      val funTbl = LCPS.FunTbl.mkTable (32, SyntacticInfo)
      val varTbl = LV.Tbl.mkTable (32, SyntacticInfo)

      fun newVar function (var, ty) =
            LV.Tbl.insert varTbl
              (var, { ty=ty, def=function, uses=LCPS.FunSet.empty })
      fun useVar function (CPS.VAR var) =
            let val { ty, def, uses } = LV.Tbl.lookup varTbl var
                                        handle SyntacticInfo => (print
                                        (LV.lvarName var ^ " missing\n");
                                         raise SyntacticInfo)
                val uses' = LCPS.FunSet.add (uses, function)
            in  LV.Tbl.insert varTbl (var, { ty=ty, def=def, uses=uses' })
            end
        | useVar function _ = ()

      fun walkF parent (function as (kind, name, args, tys, body): LCPS.function) =
        let val () = ListPair.appEq (newVar function) (args, tys)
            val fv = subtracts (walkE function body, args)
        in  LCPS.FunTbl.insert funTbl (function, { binder=parent, fv=fv });
            fv
        end
      and walkE currF =
        let
          val newVar' = newVar currF
          val useVar' = useVar currF
          fun exp (LCPS.FIX (_, bindings, cexp)) =
                let val names = map #2 bindings
                    val () = app (fn (kind, name, _, _, _) =>
                                    newVar currF (name, kindToCty kind))
                                 bindings
                    val fvs = map (walkF (SOME currF)) bindings
                    val fv  = exp cexp
                    val fv' = foldr LV.Set.union fv fvs
                in  subtracts (fv', names)
                end
            | exp (LCPS.APP (_, f, args)) =
                (app useVar' (f :: args);
                 addVs (LV.Set.empty, f :: args))
            | exp (LCPS.RECORD (_, _, values, v, cexp)) =
                let val used = map #2 values
                    val defd = map #1 values
                in  newVar' (v, CPS.PTRt (CPS.RPT (List.length values)));
                    app (fn v => newVar' (v, CPSUtil.BOGt)) defd;
                    app useVar' used;
                    addVs (subtract (exp cexp, v), used)
                end
            | exp (LCPS.SELECT (_, _, arg, x, ty, cexp)) =
                (useVar' arg; newVar' (x, ty);
                 addV (subtract (exp cexp, x), arg))
            | exp (LCPS.OFFSET _) = raise Fail "offset"
            | exp (LCPS.SWITCH (_, value, _, branches)) =
                let val fvs = map exp branches
                    val fv  = foldr LV.Set.union LV.Set.empty fvs
                in  useVar' value; addV (fv, value)
                end
            | exp (LCPS.BRANCH (_, _, args, _, expT, expF)) =
                let val fv = LV.Set.union (exp expT, exp expF)
                in  app useVar' args; addVs (fv, args)
                end
            | exp (LCPS.SETTER (_, _, args, cexp)) =
                (app useVar' args; addVs (exp cexp, args))
            | exp (LCPS.PURE   (label, CPS.P.MAKEREF, values, x, ty, cexp)) =
                (* GROSS HACK *)
                (newVar' (label, CPSUtil.BOGt);
                 app useVar' values; newVar' (x, ty);
                 addVs (subtract (exp cexp, x), values))
            | exp (LCPS.LOOKER (_, _, values, x, ty, cexp) |
                   LCPS.ARITH  (_, _, values, x, ty, cexp) |
                   LCPS.PURE   (_, _, values, x, ty, cexp)) =
                (app useVar' values; newVar' (x, ty);
                 addVs (subtract (exp cexp, x), values))
            | exp (LCPS.RCC (_, _, _, _, args, returns, cexp)) =
                (app useVar' args; app newVar' returns;
                 addVs (subtracts (exp cexp, map #1 returns), args))
        in
          exp
        end
    in
      walkF NONE cps; T { funTbl=funTbl, varTbl=varTbl, lam0=cps }
    end

  fun typeof (T { varTbl, lam0, ... }) v =
    if LV.same (#2 lam0, v) then
      CPS.FUNt
    else
      #ty (LV.Tbl.lookup varTbl v)
  fun definitionSite (T { varTbl, lam0, ... }) v =
    if LV.same (#2 lam0, v) then
      raise Fail "TODO"
    else
      #def (LV.Tbl.lookup varTbl v)
  fun useSites (T { varTbl, lam0, ... }) v =
    if LV.same (#2 lam0, v) then
      LCPS.FunSet.empty
    else
      #uses (LV.Tbl.lookup varTbl v)
      handle SyntacticInfo => (print (LV.lvarName v ^ " missing\n");
                               raise SyntacticInfo)

  fun binderOf (T { funTbl, ... }) = #binder o LCPS.FunTbl.lookup funTbl
  fun fv (T { funTbl, ... }) = #fv o LCPS.FunTbl.lookup funTbl

  fun dump (T { funTbl, varTbl, ... }) =
    let val p = print
        fun lst xs = "[" ^ String.concatWith ", " xs ^ "]"
        val funName = LV.lvarName o (#2: LCPS.function -> LCPS.lvar)
        fun pF (function: LCPS.function, { binder, fv }) =
          (p ("fun " ^ funName function ^  ": ");
           p (case binder
                of NONE => "toplevel"
                 | SOME p => "inside " ^ funName p);
           p "; ";
           p ("fv: " ^ lst (map LV.lvarName (LV.Set.listItems fv)));
           p "\n")
        fun pV (var, { ty, def, uses }) =
          (p ("var " ^ LV.lvarName var ^ CPSUtil.ctyToString ty ^ ": ");
           p ("defined in " ^ funName def ^ "; ");
           p ("used in " ^
              lst (map funName (LCPS.FunSet.listItems uses)));
           p "\n")
    in  p "=========== Syntactic Info =============\n";
        LCPS.FunTbl.appi pF funTbl;
        LV.Tbl.appi pV varTbl;
        p "========================================\n"
    end
end
