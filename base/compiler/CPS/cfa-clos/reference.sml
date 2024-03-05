functor RefClosureFn(MachSpec : MACH_SPEC) :> sig
  val convert : LabelledCPS.function * CallGraph.t * SyntacticInfo.t
                -> LabelledCPS.function
end = struct
  structure CG   = CallGraph
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar
  structure Syn  = SyntacticInfo
  structure FunMonoSet = LCPS.FunMonoSet

  val nCalleeSaves = MachSpec.numCalleeSaves
  val nGPArgRegs   = MachSpec.numArgRegs
  val nFPArgRegs   = MachSpec.numFloatArgRegs
  val nGPRegs      = MachSpec.numRegs
  val nFPRegs      = MachSpec.numFloatRegs
  val unboxedFloats = MachSpec.unboxedFloats

  fun isFirstOrder (cg, info) function =
    let val name = LCPS.nameOfF function
        fun isF (CPS.VAR x) = LV.same (name, x)
          | isF _ = false
        fun isCallee (LCPS.APP (_, f, args)) = not (List.exists isF args)
          | isCallee _ = false
    in  case CG.info cg function
          of CG.Known _ => LCPS.Set.all isCallee (Syn.usePoints info name)
           | (CG.Family _ | CG.Escape) => false
           | CG.Unreachable => (print ("warning: " ^ LV.lvarName name ^ "\n");
                                false)
    end

  fun assignFunKind (cps, cg, info) =
    let
      val isFO = isFirstOrder (cg, info)
      fun fixF nrecs (f as (CPS.CONT, name, args, tys, body)) =
            if isFO f then
              (CPS.KNOWN_CONT, name, args, tys, fixE body)
            else
              (CPS.CONT, name, args, tys, fixE body)
        | fixF nrecs (f as (kind, name, args, tys as (CPS.CNTt::_), body)) =
            if isFO f then
              if nrecs = 1 then
                (CPS.KNOWN, name, args, tys, fixE body)
              else
                (CPS.KNOWN_REC, name, args, tys, fixE body)
            else
              (CPS.ESCAPE, name, args, tys, fixE body)
        | fixF nrecs (f as (kind, name, args, tys, body)) =
            if isFO f then
              (CPS.KNOWN_TAIL, name, args, tys, fixE body)
            else
              raise Fail "escaping-fun has no continuations"
      and fixE cexp =
        case cexp
          of LCPS.FIX (label, bindings, e) =>
               let val nrecs = List.length bindings
               in  LCPS.FIX (label, map (fixF nrecs) bindings, fixE e)
               end
           | LCPS.APP _ => cexp
           | LCPS.RECORD (label, rk, elems, name, e) =>
               LCPS.RECORD (label, rk, elems, name, fixE e)
           | LCPS.SELECT (label, n, v, x, ty, e) =>
               LCPS.SELECT (label, n, v, x, ty, fixE e)
           | LCPS.OFFSET _ => raise Fail "offset"
           | LCPS.SWITCH (label, v, x, branches) =>
               LCPS.SWITCH (label, v, x, map fixE branches)
           | LCPS.BRANCH (label, b, args, x, con, alt) =>
               LCPS.BRANCH (label, b, args, x, fixE con, fixE alt)
           | LCPS.SETTER (label, s, args, e) =>
               LCPS.SETTER (label, s, args, fixE e)
           | LCPS.LOOKER (label, l, args, x, ty, e) =>
               LCPS.LOOKER (label, l, args, x, ty, fixE e)
           | LCPS.ARITH (label, a, args, x, ty, e) =>
               LCPS.ARITH (label, a, args, x, ty, fixE e)
           | LCPS.PURE (label, p, args, x, ty, e) =>
               LCPS.PURE (label, p, args, x, ty, fixE e)
           | LCPS.RCC (l, b, name, ty, args, res, e) =>
               LCPS.RCC (l, b, name, ty, args, res, fixE e)
    in
      fixF 1 cps
    end

  fun installStageNumbers (cps, cg, info) =
    let
      exception StageNum
      val snTbl = LCPS.FunTbl.mkTable (32, StageNum)
      val find = LCPS.FunTbl.find snTbl
      val lookup = LCPS.FunTbl.lookup snTbl
      val insert = LCPS.FunTbl.insert snTbl
      val components = CG.scc cg
      fun maxMap f = List.foldl (fn (x, acc) => Int.max (f x, acc)) 0
      fun maxSNOfPred function =
        let val preds = CG.predecessors cg function
        in  maxMap (fn f => Option.getOpt (find f, ~1)) preds
        end
      fun assign (CG.Single f) =
            insert (f, maxSNOfPred f + 1)
        | assign (CG.Group fs) =
            let val maxSN = maxMap maxSNOfPred fs
                val sn = maxSN + 1
            in  app (fn f => insert (f, sn)) fs
            end
    in
      app assign components;
      snTbl
    end

  fun dumpStageNumbers snTbl =
    let fun p (f: LCPS.function, n) =
          print ("\t" ^ LV.lvarName (#2 f) ^ "--->" ^ Int.toString n ^ "\n")
    in  LCPS.FunTbl.appi p snTbl
    end

  fun convert (cps, cg, info)  =
    let
      val cps = assignFunKind (cps, cg, info)
      val () = (print ">>>after fk\n"; PPCps.printcps0 (LCPS.unlabelF cps);
                print "<<<after fk\n")
      val sn = installStageNumbers (cps, cg, info)
      val () = dumpStageNumbers sn
    in
      cps
    end
end
