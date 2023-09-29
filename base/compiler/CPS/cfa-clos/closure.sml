(* closure.sml
 *
 * Closure-convert a CPS function.
 *)

signature CLOSURE = sig
  val closeCPS : CPS.function -> CPS.function
end (* signature CLOSURE *)

functor Closure(MachSpec : MACH_SPEC) : CLOSURE = struct
  exception Unimp

  fun test cps =
    let
      val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n")
      val lcps = LabelledCPS.labelF cps
      val callgraph = CallGraph.new ()
      val analyze = ZeroCFA.analyze lcps
    in
      ()
    end

  fun closeCPS cps = (test cps; raise Unimp)

end
