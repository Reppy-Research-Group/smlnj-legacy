(* closure.sml
 *
 * Closure-convert a CPS function.
 *)

(* signature CLOSURE = sig *)
(*   val closeCPS : CPS.function -> CPS.function *)
(* end (1* signature CLOSURE *1) *)

functor CFAClosure(MachSpec : MACH_SPEC) : CLOSURE = struct
  exception Unimp

  structure ClosureRep = ClosureRepFn(MachSpec)
  structure CG   = CallGraph
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar

  fun dumpSCC components =
    let
      fun p (CallGraph.SINGLE f) =
           print ("[" ^ LambdaVar.lvarName (#2 f) ^ "]\n")
        | p (CallGraph.GROUP g) =
           print ("[" ^ String.concatWithMap "," (LambdaVar.lvarName o #2) g ^ "]\n")
    in
      app p components
    end

  fun test cps =
    let
      (* val cps = #1 (FreeClose.freemapClose cps) *)
      val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n")
      val lcps = LabelledCPS.labelF cps
      val syntactic = SyntacticInformation.calculate lcps
      val () = SyntacticInformation.dump syntactic
      val callgraph = ZeroCFA.analyze lcps
      (* val scc = CallGraph.scc callgraph *)
      (* val cg  = CallGraph.callGraphDot callgraph *)
      (* val web = CallGraph.callWebDot callgraph *)
      (* val (lcps, lifetime) = Lifetime.analyze (lcps, callgraph) *)
      (* val slots = ClosureRep.analyze (lcps, callgraph, lifetime) *)
      (* val () = DotLanguage.dump cg *)
      (* val () = dumpSCC scc *)
    in
      ()
    end

  (* fun closeFix *)

  fun closeCPS cps =
    let
      (* val lcps = LabelledCPS.labelF cps *)
      (* val callgraph = ZeroCFA.analyze lcps *)
      (* val lifetime = Lifetime.analyze (lcps, callgraph) *)
    in
      test cps; cps
    end

end
