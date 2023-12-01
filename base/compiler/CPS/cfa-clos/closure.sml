(* closure.sml
 *
 * Closure-convert a CPS function.
 *)

(* signature CLOSURE = sig *)
(*   val closeCPS : CPS.function -> CPS.function *)
(* end (1* signature CLOSURE *1) *)

functor CFAClosure(MachSpec : MACH_SPEC) : CLOSURE = struct
  exception Unimp

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
      (* val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n") *)
      val lcps = LabelledCPS.labelF cps
      val callgraph = ZeroCFA.analyze lcps
      val scc = CallGraph.scc callgraph
      val () = dumpSCC scc
    in
      ()
    end

  fun closeCPS cps = (test cps; cps)

end
