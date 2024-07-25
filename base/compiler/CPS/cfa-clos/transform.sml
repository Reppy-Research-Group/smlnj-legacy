structure Transform :> sig
  val transform : LCPS.function * ClosureDecision.t -> LCPS.function
end = struct
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo

  datatype path = Path of { base: LV.lvar, selects: int list }

  fun pathToS (Path {base, selects}) =
    concat (LV.lvarName base :: map (fn i => "." ^ Int.toString i) selects)

  fun tagInt i =
    CPS.NUM { ival=IntInf.fromInt i, ty={ sz=Target.defaultIntSz, tag=true }}

  fun slotToVal (D.EnvID e) = CPS.VAR (D.EnvID.unwrap e)
    | slotToVal (D.Var v) = CPS.VAR v
    | slotToVal (D.Code v) = CPS.LABEL v
    | slotToVal D.Null = tagInt 0

  structure Context :> sig
    type t

    type frag =
      t * LCPS.fun_kind * LCPS.lvar * LCPS.lvar list * LCPS.cty list * LCPS.cexp

    val newFun : LCPS.function -> frag
    val expand : t * LCPS.value list -> LCPS.value list

    val dump : t -> unit
  end = struct
    datatype t = T of {
      access: P.path LV.Map.map,
      protocol: D.slot list LV.Map.map,
      inscope: LV.Set.set
    }

    fun dump (T {access, protocol, inscope}) =
      let
        val p = app print
        val cwm = String.concatWithMap
        fun paccess (v, path) =
          p ["  ", LV.lvarName v, " --> ", pathToS path, "\n"]
        fun pprotocol (v, ss) =
          p ["  ", LV.lvarName v, " --> [", cwm "," D.slotToString ss, "]\n"]
      in
        p ["== Access ==\n"];
        LV.Map.appi paccess access;
        p ["== Protocol ==\n"];
        LV.Map.appi pprotocol access;
        p ["== InScope ==\n"];
        p ["[", cwm "," LV.lvarName inscope, "]"]
      end
  end

  fun transform (cps, D.T {repr, allo, heap}) = raise Fail ""
end
