structure Web :> sig
  type id
  type t

  val calculate : FlowCFA.result * SynataticInfo.t -> t

  val webOfVar : t * LabelledCPS.lvar -> id
  val webOfFun : t * LabelledCPS.function -> id

  datatype kind = User | Cont

  val defs : id -> LabelledCPS.function vector
  val uses : id -> LabelledCPS.lvar vector
  val content : id -> { defs: LabelledCPS.function vector,
                        uses: LabelledCPS.lvar vector }
  val polluted : id -> bool
  val kind : id -> kind

end = struct

  structure S = SyntaticInfo

  type id = int

  datatype kind = User | Cont

  type info = {
    defs: LCPS.function vector,
    uses: LCPS.lvar vector,
    polluted: bool,
    kind: kind
  }

  datatype t = T of {
    webs: info vector,
    funMap: id LCPS.FunTbl.tbl,
    varMap: id LV.Tbl.tbl
  }

  datatype either = datatype Either.either

  fun calculate ({lookup, escape}, syn) =
    let
      type item = (LCPS.var, LCPS.function) either

      fun maximize ([], defs, uses, polluted) = (defs, uses, polluted)
        | maximize (INL v :: todo', defs, uses, polluted) =
            if LV.Set.member (uses, v) then
              maximize (todo', defs, uses, polluted)
            else
              (case lookup v
                 of NONE => (* v is dead, can this even be possible? *)
                      raise Fail "Impossible dead variable in a web"
                  | SOME { known, unknown } =>
                      let val defs = LCPS.FunSet.addList (defs, known)
                          val uses = LV.Set.add (uses, v)
                          val polluted = polluted orelse unknown
                      in  maximize (todo', defs, uses, polluted)
                      end)
        | maximize (INR f :: todo', defs, uses, polluted) =
            if LCPS.FunSet.member (defs, f) then
              maximize (todo', defs, uses, polluted)
            else
              let val { known, escape } = flow f
                  val uses = LV.Set.addList (uses, known)
                  val defs = LCPS.FunSet.add (defs, f)
                  val polluted = polluted orelse escape
              in  maximize (todo', defs, uses, polluted)
              end

      val funMap = LCPS.FunTbl.mkTable (1024, Fail "funmap")
      val varMap = LV.Tbl.mkTable (1024, Fail "varmap")

      fun processFun (f, (length, webs: info list)) =
        if LCPS.FunTbl.inDomain funMap f then
          (length, webs)
        else
          let val web as (defs, uses, polluted) =
                maximize ([INR f], LCPS.FunSet.empty, LV.Set.empty, false)
              val defs = LCPS.FunSet.toList defs and uses = LV.Set.toList uses
              val kind =
                (case #1 (List.hd defs)
                   of (CPS.CONT | CPS.KNOWN_CONT) => Cont
                    | _ => User)
              val id = length
              val () = List.app (fn f => LCPS.FunTbl.insert funMap (f, id)) defs
              val () = List.app (fn v => LV.Tbl.insert varMap (v, id)) uses
              val web = { defs=Vector.fromList defs, uses=Vector.fromList uses,
                          polluted=polluted, kind=kind }
          in  (length + 1, web :: webs)
          end
    in
      raise Fail "TODO"
    end
end
