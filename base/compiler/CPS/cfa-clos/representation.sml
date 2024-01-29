functor ClosureRepFn(MachSpec : MACH_SPEC) :> sig
  (* type lvar = LabelledCPS.lvar *)
  (* datatype rep = REP of { slots: lvar list, heap: lvar list } *)
  val analyze : LabelledCPS.function * CallGraph.t * Lifetime.t
             -> LabelledCPS.function -> int
end = struct
  structure CG   = CallGraph
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar

  type lvar = LabelledCPS.lvar datatype rep = REP of { slots: lvar list, heap: lvar list }

  val nCalleeSaves = MachSpec.numCalleeSaves
  val nRegs        = MachSpec.numRegs

  fun dumpSlots (callgraph, slots) =
    Vector.app
      (fn f =>
        print (LV.lvarName (#2 f) ^ "\t" ^ Int.toString (slots f) ^ "\n"))
      (CG.allFunctions callgraph)

  fun sameFun (f1, f2) = LV.same (LCPS.nameOfF f1, LCPS.nameOfF f2)

  fun calculateSlots (function, callgraph, lifetime) =
    let
      val insert = LCPS.FunTbl.insert
      val find   = LCPS.FunTbl.find
      val lookup = LCPS.FunTbl.lookup

      fun standardSlots (f as (funkind, _, _, _, _)) =
        case funkind
          of (CPS.CONT | CPS.KNOWN_CONT) => nCalleeSaves
           | _ => (* all others are user functions *) 1

      fun initTbl functions =
        let
          val tbl = LCPS.FunTbl.mkTable (1024, Fail "slots")
          fun assign (f as (funkind, _, args, _, _)) =
            case CG.info callgraph f
              of (CG.ESCAPE | CG.UNREACHABLE) =>
                   insert tbl (f, standardSlots f)
               | CG.PROTOCOL _ => (* TODO: PROTOCOL *)
                   insert tbl (f, standardSlots f)
               | _ =>
                   insert tbl (f, nRegs - List.length args)
        in
          Vector.app assign functions; tbl
        end

      fun loop tbl functions =
        let
          fun go n =
            let
              val changed = ref false
              fun minMapOpt f =
                Vector.foldl (fn (x, acc) =>
                  case f x
                    of SOME n => Int.min (n, acc)
                     | NONE => acc)
              fun visit f =
                let
                  fun isFreeIn (g, v) =
                    LV.Map.inDomain (lookup lifetime g, v)
                  fun removeFreeInF f fvG =
                    let val fvF = LV.Map.listKeys (lookup lifetime f)
                    in  foldl (fn (v, fvG) =>
                                case LV.Map.findAndRemove (fvG, v)
                                  of SOME (fvG', _) => fvG'
                                   | NONE => fvG)
                              fvG fvF
                    end
                  fun isBinderOfF g =
                    case CG.binderOfF callgraph f
                      of SOME g' => sameFun (g, g')
                       | NONE => false
                  fun constraint g =
                    if isBinderOfF g then
                      NONE
                    else
                      let val fvG = lookup lifetime g
                          val ndiff = LV.Map.numItems (removeFreeInF f fvG)
                      in  SOME (Int.max (standardSlots f, lookup tbl g - ndiff))
                      end
                  fun update (old, new) =
                    if old = new then
                      ()
                    else
                      (changed := true; insert tbl (f, new))
                in
                  case CG.info callgraph f
                    of (CG.ESCAPE | CG.UNREACHABLE) => ()
                     | CG.WELLKNOWN callers =>
                         let val nSlots = lookup tbl f
                             val nSlots' = minMapOpt constraint nSlots callers
                         in  update (nSlots, nSlots')
                         end
                     | CG.PROTOCOL callers =>
                         (* TODO: PROTOCOL *)
                         ()
                         (* let val nSlots = lookup tbl f *)
                         (*     val nSlots' = minMapOpt constraint nSlots *)
                         (*                     (Vector.map #caller callers) *)
                         (* in  update (nSlots, nSlots') *)
                         (* end *)
                end
            in
              Vector.app visit functions; if !changed then go (n + 1) else ()
            end
        in
          go 0
        end
      fun colleagueConstraint tbl f =
        let
          fun constraint ({colleagues, ...}: CG.caller_info, nSlots) =
            case colleagues
              of NONE =>
                   (* a call site calling f that also calls TOP *)
                   standardSlots f
               | SOME gs =>
                   Vector.foldl
                     (fn (g, acc) => Int.min (lookup tbl g, acc))
                     nSlots gs
        in
          case CG.info callgraph f
            of CG.PROTOCOL callers =>
                 insert tbl (f, Vector.foldl constraint (lookup tbl f) callers)
             | _ => ()
        end
      (* fun numArgsConstraint tbl f = *)
      (*   let *)
      (*     fun constraint (f as (kind, name, args, tys, _)) = *)
      (*       let val nslot = lookup tbl f *)
      (*           val argslots = foldl (fn (x, CPS.FUNt) => *)
      val functions = CG.allFunctions callgraph
      val tbl = initTbl functions
    in
      loop tbl functions;
      Vector.app (colleagueConstraint tbl) functions;
      LCPS.FunTbl.lookup tbl
    end

  val _ =
    calculateSlots: LabelledCPS.function * CallGraph.t * Lifetime.t
                    -> (LabelledCPS.function -> int)

  datatype object
    = Value of LCPS.cty
    | WellKnown of { function: LCPS.function,
                     csg:  LCPS.lvar list,
                     csf:  LCPS.lvar list,
                     heap: LCPS.lvar list }
    | Known of { functions: LCPS.function list,
                 ncsg: LCPS.lvar list,
                 ncsf: LCPS.lvar list }

  fun analyze (function, callgraph, lifetime) =
    let
      val slots = calculateSlots (function, callgraph, lifetime)
    in
      print ("nRegs: " ^ Int.toString nRegs ^ ", " ^ Int.toString nCalleeSaves ^ ", "
                       ^ Int.toString MachSpec.numFloatRegs ^ ", " ^ Int.toString MachSpec.numFloatCalleeSaves
                       ^ "\n");
      print ("unboxedfloats: " ^ Bool.toString MachSpec.unboxedFloats ^ "\n");
      print ("Escaping Lambda: " ^ String.concatWithMap ", " (LV.lvarName o #2)
      (Vector.toList (CG.escapingFunctions callgraph)) ^ "\n");
      dumpSlots (callgraph, slots);
      slots
    end
end
