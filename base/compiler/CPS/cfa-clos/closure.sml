(* closure.sml
 *
 * Closure-convert a CPS function.
 *)

(* signature CLOSURE = sig *)
(*   val closeCPS : CPS.function -> CPS.function *)
(* end (1* signature CLOSURE *1) *)

functor CFAClosure(MachSpec : MACH_SPEC) : CLOSURE = struct
  exception Unimp

  (* structure ClosureRep = ClosureRepFn(MachSpec) *)
  (* structure CG   = CallGraph *)
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar
  (* structure RefClosure = RefClosureFn(MachSpec) *)
  structure Cheat = Closure(MachSpec)
  structure Pipeline = ClosureDecisionPipeline(MachSpec)
  structure Config = Control.NC

  (* fun dumpSCC components = *)
  (*   let *)
  (*     fun p (CallGraph.Single f) = *)
  (*          print ("[" ^ LambdaVar.lvarName (#2 f) ^ "]\n") *)
  (*       | p (CallGraph.Group g) = *)
  (*          print ("[" ^ String.concatWithMap "," (LambdaVar.lvarName o #2) g ^ "]\n") *)
  (*   in *)
  (*     app p components *)
  (*   end *)

  fun timeit str f x =
    let
      val start = Time.now ()
      val result = f x
      val stop = Time.now ()
      val diff = Time.- (stop, start)
      val () = app print ["Timing: ", str, " ", Time.toString diff, "\n"]
    in
      result
    end
  (* fun timeit' msg thnk x = *)
  (*   let val start = Timer.startCPUTimer () *)
  (*       val result = thnk x *)
  (*       val { nongc={usr, sys}, gc={usr=gcusr, sys=gcsys} } = *)
  (*         Timer.checkCPUTimes start *)
  (*       val tos = Time.toString *)
  (*   in  app print [msg, ": usr=", tos usr, " sys=", tos sys, *)
  (*                  " gcusr=", tos gcusr, " gcsys=", tos gcsys, "\n"]; *)
  (*       result *)
  (*   end *)

  fun timeit _ f x = f x

  fun phase x = Stats.doPhase (Stats.makePhase x)

  fun test cps =
    let
      (* val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n") *)
      val lcps = timeit "label" LabelledCPS.labelF cps
        handle e => (print "1\n"; raise e)
      val syntactic = timeit "syntactic" SyntacticInfo.calculate lcps
        handle e => (print "2\n"; raise e)
      (* val () = SyntacticInfo.dump syntactic *)
      (* val callgraph = ZeroCFA.analyze (syntactic, lcps) *)
      val result = timeit "flow-cfa" FlowCFA.analyze (syntactic, lcps)
        handle e => (print "3\n"; raise e)
      (* val () = ClosureDecision.dump (decision, syntactic) *)
      val web = timeit "web" Web.calculate (result, syntactic)
        handle e => (print "5\n"; raise e)
      val () = if !Config.dumpWeb then Web.dump web else ()

      (* val () = Lifetime.analyze (lcps, syntactic) *)
      val (funtbl, looptbl) =
        timeit "control-flow" ControlFlow.analyze (lcps, syntactic, result)
      val shr =
        timeit "sharing" SharingAnalysis.analyze (lcps, syntactic, funtbl, looptbl)

      val decision =
        if !Config.flatClosure then
          timeit "flat-closure" FlatClosureDecision.produce (lcps, syntactic)
        else
          timeit "pipe" Pipeline.pipeline (lcps, syntactic, web, shr, funtbl, looptbl)
        handle e => (print "6\n"; raise e)
      val () =
        if !Config.dumpDecision then ClosureDecision.dump (decision, syntactic) else ()
      val lcps =
        timeit "transform" Transform.transform (lcps, decision, web, syntactic)
        handle e => (print "7\n"; raise e)
      val lcps =
        timeit "avail exp" AvailableExpression.transform lcps
        handle e => (print "8\n"; raise e)
      (* val () = (print "RESULT >>>>>\n"; PPCps.printcps0 (LCPS.unlabelF lcps'); print "<<<<<\n") *)

      (* val decision = timeit "flat" FlatClosureDecision.produce (lcps, syntactic) *)
      (* handle e => (print "4\n"; raise e) *)
      (* val lcps = timeit "transform" Transform.transform (lcps, decision, web, syntactic) *)
      (* handle e => (print "6\n"; raise e) *)
      (* val () = InvariantChecker.check (decision', syntactic) *)
    in
      UnRebind.unrebind (LCPS.unlabelF lcps)
      (* Cheat.closeCPS cps *)
    end
    handle e =>
    (let
     val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n")
     in   raise e
     end)

  (* fun closeFix *)

  fun closeCPS cps =
    let
      val () = print "[new] "
      (* val lcps = LabelledCPS.labelF cps *)
      (* val callgraph = ZeroCFA.analyze lcps *)
      (* val lifetime = Lifetime.analyze (lcps, callgraph) *)
    in
      test cps
    end

end
