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

  (* fun dumpSCC components = *)
  (*   let *)
  (*     fun p (CallGraph.Single f) = *)
  (*          print ("[" ^ LambdaVar.lvarName (#2 f) ^ "]\n") *)
  (*       | p (CallGraph.Group g) = *)
  (*          print ("[" ^ String.concatWithMap "," (LambdaVar.lvarName o #2) g ^ "]\n") *)
  (*   in *)
  (*     app p components *)
  (*   end *)

  fun test cps =
    let
      (* val cps = #1 (FreeClose.freemapClose cps) *)
      val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n")
      val lcps = LabelledCPS.labelF cps
      val syntactic = SyntacticInfo.calculate lcps
      (* val () = SyntacticInfo.dump syntactic *)
      (* val callgraph = ZeroCFA.analyze (syntactic, lcps) *)
      val result = FlowCFA.analyze (syntactic, lcps)
      val decision = FlatClosureDecision.produce (lcps, syntactic)
      val () = ClosureDecision.dump (decision, syntactic)
      val web = Web.calculate (result, syntactic)
      val () = Web.dump web

      val lcps = Transform.transform (lcps, decision, web, syntactic)

      val () = print "RESULT:\n>>>>>>\n"
      val () = PPCps.printcps0 (LCPS.unlabelF lcps)
      val () = print "<<<<<<\n"

      (* val repr = ClosureRep.initialize *)
      (*              {cps=lcps, syn=syntactic, lookup=lookup, escape=escape} *)
      (* val () = ClosureRep.dumpGraph repr *)
      (* val () = CG.dumpStats callgraph *)
      (* val f  = RefClosure.convert (lcps, callgraph, syntactic) *)
      (* val () = ClosureRep.analyze (lcps, callgraph, syntactic) *)
      (* val scc = CallGraph.scc callgraph *)
      (* val cg  = CallGraph.callGraphDot callgraph *)
      (* val web = CallGraph.callWebDot callgraph *)
      (* val (lcps, lifetime) = Lifetime.analyze (lcps, callgraph) *)
      (* val slots = ClosureRep.analyze (lcps, callgraph, lifetime) *)
      (* val () = DotLanguage.dump cg *)
      (* val () = dumpSCC scc *)
    in
      UnRebind.unrebind (LCPS.unlabelF lcps)
      (* Cheat.closeCPS cps *)
    end

  (* fun closeFix *)

  fun closeCPS cps =
    let
      (* val lcps = LabelledCPS.labelF cps *)
      (* val callgraph = ZeroCFA.analyze lcps *)
      (* val lifetime = Lifetime.analyze (lcps, callgraph) *)
    in
      test cps
    end

end
