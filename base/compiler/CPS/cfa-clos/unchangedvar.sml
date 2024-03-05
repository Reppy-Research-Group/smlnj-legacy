structure UnchangedVariable :> sig
  val analyze : LabelledCPS.function * CallGraph.t * SyntacticInfo.t ->
                LabelledCPS.function -> LambdaVar.Set.set
end = struct
  structure LV = LambdaVar
  structure CG = CallGraph
  structure LCPS = LabelledCPS

  fun isFirstOrder (callgraph, name) (f: LCPS.function) =
    let fun exp (LCPS.FIX (_, bindings, e)) = exp e
          | exp (LCPS.APP (_, CPS.VAR f, _)) =
              (case CG.whatis callgraph f
                 of CG.FirstOrder function => true
                  | CG.Function functions =>
                      List.all (fn CG.Out => true
                                 | (CG.In g) => not (LV.same (name, #2 g)))
                               functions
                  | _ => true)
          | exp (LCPS.APP (_, _, _)) = true
          | exp (LCPS.SWITCH (_, _, _, es)) =
              foldl (fn (e, acc) => acc andalso exp e) true es
          | exp (LCPS.BRANCH (_, _, _, _, te, fe)) = exp te andalso exp fe
          | exp (LCPS.RECORD (_, _, _, _, e) |
                 LCPS.SELECT (_, _, _, _, _, e) |
                 LCPS.OFFSET (_, _, _, _, e) |
                 LCPS.SETTER (_, _, _, e) |
                 LCPS.LOOKER (_, _, _, _, _, e) |
                 LCPS.ARITH  (_, _, _, _, _, e) |
                 LCPS.PURE   (_, _, _, _, _, e) |
                 LCPS.RCC    (_, _, _, _, _, _, e)) = exp e
    in  exp (#5 f)
    end

  (* Very crude unchanged variable analysis:
   * If a function is used as a first order function, then all of its free
   * variables can be argument-passed; if not, none of the free variables can.
   *
   * TODO: Implement Lightweight Closure Conversion for real.
   *)
  fun analyze (cps, callgraph, info) =
    fn f =>
      case CG.info callgraph f
        of CG.Known { callers } =>
             if List.all (isFirstOrder (callgraph, #2 f)) callers then
               (SyntacticInfo.fv info f, LV.Set.empty)
             else
               (LV.Set.empty, SyntacticInfo.fv info f)
         | _ => (LV.Set.empty, SyntacticInfo.fv info f)
end
