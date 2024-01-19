structure Lifetime :> sig
  type fvinfo = LabelledCPS.lvar * int * int
  type fv = (int * int) LambdaVar.Map.map
  type stage_num = int
  val analyze : LabelledCPS.function * CallGraph.t ->
                LabelledCPS.function * fv LabelledCPS.FunTbl.hash_table
end = struct
  type fvinfo = LabelledCPS.lvar * int * int
  type fv = (int * int) LambdaVar.Map.map
  type stage_num = int
  structure CG   = CallGraph
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar

  fun installStageNum (function, callgraph) =
    (* TODO: Can this be done in one pass? *)
    (* TODO: Calculate stage num using flow info? *)
    let
      val tbl = LCPS.FunTbl.mkTable (1024, Fail "stagenum")
      val lookup = LCPS.FunTbl.lookup tbl
      val insert = LCPS.FunTbl.insert tbl

      fun visitF f =
        let fun exp (LCPS.FIX (_, bindings, e)) = (app f bindings; exp e)
              | exp (LCPS.APP (_, f, args)) = ()
              | exp (LCPS.SWITCH (_, _, _, es)) = app exp es
              | exp (LCPS.BRANCH (_, _, _, _, te, fe)) = (exp te; exp fe)
              | exp (LCPS.RECORD (_, _, _, _, e) |
                     LCPS.SELECT (_, _, _, _, _, e) |
                     LCPS.OFFSET (_, _, _, _, e) |
                     LCPS.SETTER (_, _, _, e) |
                     LCPS.LOOKER (_, _, _, _, _, e) |
                     LCPS.ARITH  (_, _, _, _, _, e) |
                     LCPS.PURE   (_, _, _, _, _, e) |
                     LCPS.RCC    (_, _, _, _, _, _, e)) = exp e
        in  exp
        end

      fun install sn (function as (_, _, _, _, body)) =
        (insert (function, sn + 1); visitF (install (sn + 1)) body)

      fun maxMap f = Vector.foldl (fn (x, acc) => Int.max (f x, acc)) 0

      fun updateCont sn
                     (function as ((CPS.CONT|CPS.KNOWN_CONT), _, _, _, body)) =
          let
            val maxPred = case CG.info callgraph function
                            of CG.WELLKNOWN preds => maxMap lookup preds
                             | CG.PROTOCOL callers =>
                                 maxMap (lookup o #caller) callers
                             | (CG.UNREACHABLE | CG.ESCAPE) => 0
            val max = 1 + Int.max (sn, maxPred)
          in
            insert (function, max); visitF (updateCont max) body
          end
        | updateCont sn (function as (_, _, _, _, body)) =
            (insert (function, 1 + sn); visitF (updateCont (1 + sn)) body)
    in
      install 0 function; updateCont 0 function; lookup
    end

  fun dumpStageNum (stagenum, callgraph) =
    Vector.app
      (fn f =>
        print (LV.lvarName (#2 f) ^ "\t" ^ Int.toString (stagenum f) ^ "\n"))
      (CG.allFunctions callgraph)

  exception FreeVars
  fun freevars stagenum function =
    let
      type fv = (int * int) LV.Map.map
      val tbl: fv LCPS.FunTbl.hash_table = LCPS.FunTbl.mkTable (1024, FreeVars)
      fun mergeRng ((min, max), (min', max')) =
        (Int.min (min, min'), Int.max (max, max'))
      fun update sn (m, v) =
        LV.Map.insertWith mergeRng (m, v, (sn, sn))
      fun updateV sn (CPS.VAR v, m) = update sn (m, v)
        | updateV sn (_, m) = m
      val union = LV.Map.unionWith mergeRng
      val unions = foldl union LV.Map.empty
      fun remove (m, v) = case LV.Map.findAndRemove (m, v)
                            of SOME (m', _) => m'
                             | NONE => m
      fun removes (m, vs) = foldl (fn (v, acc) => remove (acc, v)) m vs

      fun fvbinding (function as (funkind, name, args, tys, body)) =
        let val fvBody = fvexp (stagenum function) body
            val fv = removes (fvBody, name :: args)
        in  LCPS.FunTbl.insert tbl (function, fv); fv
        end
      and fvexp sn =
        let
          fun exp (LCPS.FIX (_, bindings, e)) =
                let val fvs = map fvbinding bindings
                    val died = map #2 bindings
                in  removes (unions (exp e :: fvs), died)
                end
            | exp (LCPS.APP (_, f, args)) =
                foldl (updateV sn) LV.Map.empty (f :: args)
            | exp (LCPS.RECORD (_, _, values, name, e)) =
                let val used = map #2 values
                in  remove (foldl (updateV sn) (exp e) used, name)
                end
            | exp (LCPS.SWITCH (_, value, _, es)) =
                updateV sn (value, unions (map exp es))
            | exp (LCPS.BRANCH (_, _, values, _, te, fe)) =
                foldl (updateV sn) (union (exp te, exp fe)) values
            | exp (LCPS.SETTER (_, _, values, e)) =
                foldl (updateV sn) (exp e) values
            | exp (LCPS.SELECT (_, _, value, name, _, e) |
                   LCPS.OFFSET (_, _, value, name, e)) =
                remove (updateV sn (value, exp e), name)
            | exp (LCPS.LOOKER (_, _, values, name, _, e) |
                   LCPS.ARITH  (_, _, values, name, _, e) |
                   LCPS.PURE   (_, _, values, name, _, e)) =
                remove (foldl (updateV sn) (exp e) values, name)
            | exp (LCPS.RCC (_, _, _, _, values, bindings, e)) =
                let val died = map #1 bindings
                in  removes (foldl (updateV sn) (exp e) values, died)
                end
        in
          exp
        end
    in
      fvbinding function; tbl
    end

  fun dumpStageNum (stagenum, callgraph) =
    Vector.app
      (fn f =>
        print (LV.lvarName (#2 f) ^ "\t" ^ Int.toString (stagenum f) ^ "\n"))
      (CG.allFunctions callgraph)
  fun dumpFV (fv, callgraph) =
    let fun p f =
          (print (LV.lvarName (#2 f) ^ ":\n");
           LV.Map.appi (fn (v, (min, max)) =>
             print ("\t" ^ LV.lvarName v ^ "\t"
                   ^ Int.toString min ^ "\t" ^ Int.toString max ^ "\n"))
             (fv f))
    in  Vector.app p (CG.allFunctions callgraph)
    end

  fun analyze (function, callgraph) =
    let
      val stagenum = installStageNum (function, callgraph)
      val fv = freevars stagenum function
    in
      dumpStageNum (stagenum, callgraph);
      dumpFV (LCPS.FunTbl.lookup fv, callgraph);
      (function, fv)
    end
end
