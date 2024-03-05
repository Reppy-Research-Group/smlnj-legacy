functor ClosureRepFn(MachSpec : MACH_SPEC) :> sig
  (* type lvar = LabelledCPS.lvar *)
  (* datatype rep = REP of { slots: lvar list, heap: lvar list } *)
  val analyze : LabelledCPS.function * CallGraph.t * SyntacticInfo.t -> unit
end = struct
  structure CG   = CallGraph
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar
  structure Syn  = SyntacticInfo

  val nCalleeSaves = MachSpec.numCalleeSaves
  val nGPArgRegs   = MachSpec.numArgRegs
  val nFPArgRegs   = MachSpec.numFloatArgRegs
  val nGPRegs      = MachSpec.numRegs
  val nFPRegs      = MachSpec.numFloatRegs
  val unboxedFloats = MachSpec.unboxedFloats

  datatype object = Value of LCPS.lvar
                  | Label
                  | GpEnv of LCPS.lvar * int
                  | FpEnv of LCPS.lvar * int
                  | Closure of object list

  datatype rep = Rep of {
    gpslots: object list,
    fpslots: object list
  }

  val isFloatTy =
    if unboxedFloats then
      (fn (CPS.FLTt _) => true | _ => false)
    else
      (fn _ => false)

  fun isFloat info = isFloatTy o (Syn.typeof info)

  fun visitF f =
    let fun exp (LCPS.FIX (_, bindings, e)) =
              (app f bindings; app (exp o #5) bindings; exp e)
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

  exception ClosureRep
  fun bug msg = (print (msg ^ "\n"); raise ClosureRep)

  fun analyze (function as (_, _, _, _, body), callgraph, info) =
    let
      val () = print ("nGPRegs: " ^ Int.toString nGPArgRegs
                     ^"; nFPRegs: " ^ Int.toString nFPArgRegs ^ "\n")
      val tbl = LCPS.FunTbl.mkTable (1024, ClosureRep)
      val unchangedVars = UnchangedVariable.analyze (function, callgraph, info)
      val fv = Syn.fv info
      val isFloat = isFloat info
      fun debugV v = LV.lvarName v ^ CPSUtil.ctyToString (Syn.typeof info v)
      val debugVs = String.concatWithMap ", " debugV

      val components = List.rev (CallGraph.scc callgraph)

      fun lookupEnv f =
        case LCPS.FunTbl.find tbl f
          of SOME env => env
           | NONE     => bug (LV.lvarName (#2 f) ^ " no data")

      fun liftEnv fvs =
        let fun lift (v, set) =
              case CG.whatis callgraph v
                of CG.Value => LV.Set.add (set, v)
                 | CG.FirstOrder f => LV.Set.union (set, lookupEnv f)
                 | CG.Function fs =>
                     foldl (fn (CG.In f, acc) => LV.Set.union (acc, lookupEnv f)
                             | (CG.Out, acc) => acc)
                           (LV.Set.add (set, v)) fs
                 | CG.NoBinding => set
        in  LV.Set.foldl lift LV.Set.empty fvs
        end

      val () = Vector.app (fn f => LCPS.FunTbl.insert tbl (f, LV.Set.empty))
                          (CG.escapingFunctions callgraph)

      fun adjust functions =
        let
          fun initEnv f =
            let val (fvs, _) = unchangedVars f
            in  LV.Set.filter (fn v => (case CG.whatis callgraph v
                                          of (CG.FirstOrder _) => false
                                           | _ => true)) fvs
            end
          val () = Vector.app (fn f => LCPS.FunTbl.insert tbl (f, initEnv f)) functions
          fun adjustOne (f, changed) =
            let val initSlots = LCPS.FunTbl.lookup tbl f
                val name = #2 f
                val slots = liftEnv initSlots
                            handle ClosureRep => bug ("In " ^ LV.lvarName name)
                val len = LV.Set.numItems
                val changed' = changed orelse (len slots <> len initSlots)
            in
              print ("function: " ^ LV.lvarName name ^ "\n");
              print ("initSlots: " ^ debugVs (LV.Set.toList initSlots) ^ "\n");
              print ("slots: " ^ debugVs (LV.Set.toList slots) ^ "\n\n");
              changed'
            end
          fun adjustLoop () =
            let val changed = Vector.foldl adjustOne false functions
            in  if changed then adjustLoop () else ()
            end
        in
          adjustLoop ()
        end

      (* fun adjust (function as (kind, name, args, tys, body)) = *)
      (*   let val (floatArgs, gpArgs) = List.partition isFloat args *)
      (*       val (floatFV, gpFV) = LV.Set.partition isFloat (fv function) *)
      (*       val floatEnv = floatArgs @ (LV.Set.toList floatFV) *)
      (*       val gpEnv = gpArgs @ (LV.Set.toList gpFV) *)
      (*   in  print ("function: " ^ LV.lvarName name ^ "\n"); *)
      (*       print ("gp: " ^ String.concatWithMap ", " debugV gpEnv ^ "\n"); *)
      (*       print ("float: " ^ String.concatWithMap ", " debugV floatEnv ^ "\n"); *)
      (*       () *)
      (*   end *)

      (* val () = visitF adjust body *)
      val () = adjust (CallGraph.knownFunctions callgraph)
    in
      ()
    end

  (* fun dumpSlots (callgraph, slots) = *)
  (*   Vector.app *)
  (*     (fn f => *)
  (*       print (LV.lvarName (#2 f) ^ "\t" ^ Int.toString (slots f) ^ "\n")) *)
  (*     (CG.allFunctions callgraph) *)

  (* fun sameFun (f1, f2) = LV.same (LCPS.nameOfF f1, LCPS.nameOfF f2) *)

  (* fun calculateSlots (function, callgraph, lifetime) = *)
  (*   let *)
  (*     val insert = LCPS.FunTbl.insert *)
  (*     val find   = LCPS.FunTbl.find *)
  (*     val lookup = LCPS.FunTbl.lookup *)

  (*     fun standardSlots (f as (funkind, _, _, _, _)) = *)
  (*       case funkind *)
  (*         of (CPS.CONT | CPS.KNOWN_CONT) => nCalleeSaves *)
  (*          | _ => (1* all others are user functions *1) 1 *)

  (*     fun initTbl functions = *)
  (*       let *)
  (*         val tbl = LCPS.FunTbl.mkTable (1024, Fail "slots") *)
  (*         fun assign (f as (funkind, _, args, _, _)) = *)
  (*           case CG.info callgraph f *)
  (*             of (CG.ESCAPE | CG.UNREACHABLE) => *)
  (*                  insert tbl (f, standardSlots f) *)
  (*              | CG.PROTOCOL _ => (1* TODO: PROTOCOL *1) *)
  (*                  insert tbl (f, standardSlots f) *)
  (*              | _ => *)
  (*                  insert tbl (f, nRegs - List.length args) *)
  (*       in *)
  (*         Vector.app assign functions; tbl *)
  (*       end *)

  (*     fun loop tbl functions = *)
  (*       let *)
  (*         fun go n = *)
  (*           let *)
  (*             val changed = ref false *)
  (*             fun minMapOpt f = *)
  (*               Vector.foldl (fn (x, acc) => *)
  (*                 case f x *)
  (*                   of SOME n => Int.min (n, acc) *)
  (*                    | NONE => acc) *)
  (*             fun visit f = *)
  (*               let *)
  (*                 fun isFreeIn (g, v) = *)
  (*                   LV.Map.inDomain (lookup lifetime g, v) *)
  (*                 fun removeFreeInF f fvG = *)
  (*                   let val fvF = LV.Map.listKeys (lookup lifetime f) *)
  (*                   in  foldl (fn (v, fvG) => *)
  (*                               case LV.Map.findAndRemove (fvG, v) *)
  (*                                 of SOME (fvG', _) => fvG' *)
  (*                                  | NONE => fvG) *)
  (*                             fvG fvF *)
  (*                   end *)
  (*                 fun isBinderOfF g = *)
  (*                   case CG.binderOfF callgraph f *)
  (*                     of SOME g' => sameFun (g, g') *)
  (*                      | NONE => false *)
  (*                 fun constraint g = *)
  (*                   if isBinderOfF g then *)
  (*                     NONE *)
  (*                   else *)
  (*                     let val fvG = lookup lifetime g *)
  (*                         val ndiff = LV.Map.numItems (removeFreeInF f fvG) *)
  (*                     in  SOME (Int.max (standardSlots f, lookup tbl g - ndiff)) *)
  (*                     end *)
  (*                 fun update (old, new) = *)
  (*                   if old = new then *)
  (*                     () *)
  (*                   else *)
  (*                     (changed := true; insert tbl (f, new)) *)
  (*               in *)
  (*                 case CG.info callgraph f *)
  (*                   of (CG.ESCAPE | CG.UNREACHABLE) => () *)
  (*                    | CG.WELLKNOWN callers => *)
  (*                        let val nSlots = lookup tbl f *)
  (*                            val nSlots' = minMapOpt constraint nSlots callers *)
  (*                        in  update (nSlots, nSlots') *)
  (*                        end *)
  (*                    | CG.PROTOCOL callers => *)
  (*                        (1* TODO: PROTOCOL *1) *)
  (*                        () *)
  (*                        (1* let val nSlots = lookup tbl f *1) *)
  (*                        (1*     val nSlots' = minMapOpt constraint nSlots *1) *)
  (*                        (1*                     (Vector.map #caller callers) *1) *)
  (*                        (1* in  update (nSlots, nSlots') *1) *)
  (*                        (1* end *1) *)
  (*               end *)
  (*           in *)
  (*             Vector.app visit functions; if !changed then go (n + 1) else () *)
  (*           end *)
  (*       in *)
  (*         go 0 *)
  (*       end *)
  (*     fun colleagueConstraint tbl f = *)
  (*       let *)
  (*         fun constraint ({colleagues, ...}: CG.caller_info, nSlots) = *)
  (*           case colleagues *)
  (*             of NONE => *)
  (*                  (1* a call site calling f that also calls TOP *1) *)
  (*                  standardSlots f *)
  (*              | SOME gs => *)
  (*                  Vector.foldl *)
  (*                    (fn (g, acc) => Int.min (lookup tbl g, acc)) *)
  (*                    nSlots gs *)
  (*       in *)
  (*         case CG.info callgraph f *)
  (*           of CG.PROTOCOL callers => *)
  (*                insert tbl (f, Vector.foldl constraint (lookup tbl f) callers) *)
  (*            | _ => () *)
  (*       end *)
  (*     val functions = CG.allFunctions callgraph *)
  (*     val tbl = initTbl functions *)
  (*   in *)
  (*     loop tbl functions; *)
  (*     Vector.app (colleagueConstraint tbl) functions; *)
  (*     LCPS.FunTbl.lookup tbl *)
  (*   end *)

  (* val _ = *)
  (*   calculateSlots: LabelledCPS.function * CallGraph.t * Lifetime.t *)
  (*                   -> (LabelledCPS.function -> int) *)

  (* datatype object *)
  (*   = Value of LCPS.cty *)
  (*   | WellKnown of { function: LCPS.function, *)
  (*                    csg:  LCPS.lvar list, *)
  (*                    csf:  LCPS.lvar list, *)
  (*                    heap: LCPS.lvar list } *)
  (*   | Known of { functions: LCPS.function list, *)
  (*                ncsg: LCPS.lvar list, *)
  (*                ncsf: LCPS.lvar list } *)

  (* fun analyze (function, callgraph, lifetime) = raise Fail "unimp" *)
    (* let *)
    (*   val slots = calculateSlots (function, callgraph, lifetime) *)
    (* in *)
    (*   print ("nRegs: " ^ Int.toString nRegs ^ ", " ^ Int.toString nCalleeSaves ^ ", " *)
    (*                    ^ Int.toString MachSpec.numFloatRegs ^ ", " ^ Int.toString MachSpec.numFloatCalleeSaves *)
    (*                    ^ "\n"); *)
    (*   print ("unboxedfloats: " ^ Bool.toString MachSpec.unboxedFloats ^ "\n"); *)
    (*   print ("Escaping Lambda: " ^ String.concatWithMap ", " (LV.lvarName o #2) *)
    (*   (Vector.toList (CG.escapingFunctions callgraph)) ^ "\n"); *)
    (*   dumpSlots (callgraph, slots); *)
    (*   slots *)
    (* end *)
end
