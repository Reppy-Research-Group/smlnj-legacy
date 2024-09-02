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

  fun timeit str f x =
    let
      val start = Time.now ()
      val result = f x
      val stop = Time.now ()
      val diff = Time.- (stop, start)
      val () = (print (str ^ " " ^ Time.toString diff); print "\n")
    in
      result
    end

  fun timeit _ f x = f x

  fun test cps =
    let
      (* val cps = #1 (FreeClose.freemapClose cps) *)
      (* val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n") *)
      val lcps = timeit "label" LabelledCPS.labelF cps
      handle e => (print "1\n"; raise e)
      val syntactic = timeit "syntactic" SyntacticInfo.calculate lcps
      handle e => (print "2\n"; raise e)
      (* val () = SyntacticInfo.dump syntactic *)
      (* val callgraph = ZeroCFA.analyze (syntactic, lcps) *)
      val result = timeit "flow-cfa" FlowCFA.analyze (syntactic, lcps)
      handle e => (print "3\n"; raise e)
      val decision = timeit "flat" FlatClosureDecision.produce (lcps, syntactic)
      handle e => (print "4\n"; raise e)
      (* val () = ClosureDecision.dump (decision, syntactic) *)
      val web = timeit "web" Web.calculate (result, syntactic)
      handle e => (print "5\n"; raise e)
      (* val () = Web.dump web *)

      val lcps = timeit "transform" Transform.transform (lcps, decision, web, syntactic)
      handle e => (print "6\n"; raise e)

      (* val () = print "RESULT:\n>>>>>>\n" *)
      (* val () = PPCps.printcps0 (LCPS.unlabelF lcps) *)
      (* val () = print "<<<<<<\n" *)

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
    handle e => 
    (let 
     (* val () = (print ">>>>>\n"; PPCps.printcps0 cps; print "<<<<<\n") *)
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
