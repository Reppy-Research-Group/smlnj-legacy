functor RefClosureFn(MachSpec : MACH_SPEC) :> sig
  val convert : LabelledCPS.function * CallGraph.t * SyntacticInfo.t
                -> LabelledCPS.function
end = struct
  structure CG   = CallGraph
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar
  structure Syn  = SyntacticInfo
  structure FunMonoSet = LCPS.FunMonoSet

  val nGPCalleeSaves = MachSpec.numCalleeSaves
  val nFPCalleeSaves = MachSpec.numFloatCalleeSaves
  val nGPArgRegs     = MachSpec.numArgRegs
  val nFPArgRegs     = MachSpec.numFloatArgRegs
  val nGPRegs        = MachSpec.numRegs
  val nFPRegs        = MachSpec.numFloatRegs
  val unboxedFloats  = MachSpec.unboxedFloats

  val printCPS = PPCps.printcps0 o LCPS.unlabelF

  fun plength ls = print (Int.toString (List.length ls))

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
      fun fixF recs (f as (CPS.CONT, name, args, tys, body)) =
            if isFO f then
              (CPS.KNOWN_CONT, name, args, tys, fixE body)
            else
              (CPS.CONT, name, args, tys, fixE body)
        | fixF recs (f as (kind, name, args, tys as (CPS.CNTt::_), body)) =
            if isFO f then
              let val fv = Syn.fv info f
              in  if List.exists (fn r => LV.Set.member (fv, r)) recs then
                    (* (CPS.KNOWN_REC, name, args, tys, fixE body) *)
                    (CPS.KNOWN, name, args, tys, fixE body)
                  else
                    (CPS.KNOWN, name, args, tys, fixE body)
              end
            else
              (CPS.ESCAPE, name, args, tys, fixE body)
        | fixF recs (f as (kind, name, args, tys, body)) =
            if isFO f then
              (* (CPS.KNOWN_TAIL, name, args, tys, fixE body) *)
              (CPS.KNOWN, name, args, tys, fixE body)
            else
              raise Fail "escaping-fun has no continuations"
      and fixE cexp =
        case cexp
          of LCPS.FIX (label, bindings, e) =>
               let val recs = map #2 bindings
               in  LCPS.FIX (label, map (fixF recs) bindings, fixE e)
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
      fixF [#2 cps] cps
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

  datatype closure = ClosureRep of { values: CPS.value list,
                                     links : (CPS.lvar * closure) list,
                                     kind  : CPS.record_kind,
                                     id    : CPS.lvar }
  datatype protocol = KnownFunction of { label: CPS.lvar,
                                         gpfree: CPS.lvar list,
                                         fpfree: CPS.lvar list }
                    | MutualRecursion of { label: CPS.lvar,
                                           gpfree: CPS.lvar list,
                                           fpfree: CPS.lvar list }
                    | StandardFunction
                    | StandardContinuation of { callee: CPS.value,
                                                gpcs: CPS.lvar list,
                                                fpcs: CPS.lvar list }
  datatype object = Closure | CalleeSave
  datatype env = Env of { immediates: CPS.lvar list,
                          calleeSaves: CPS.lvar list,
                          closures: (CPS.lvar * closure) list,
                          (* facts *)
                          protocols: protocol LV.Map.map,
                          allocated: object LV.Tbl.hash_table,
                          cg: CG.t,
                          info: Syn.t }

  fun printEnv
    (Env { immediates, calleeSaves, closures, protocols, allocated, ...}) =
    let fun plist p l = (app (fn v => (print " "; p v)) l; print "\n")
        val pv = print o LV.lvarName
        val pval = print o PPCps.value2str
        fun pclosures (indent, l, seen) =
          let fun pc (v, ClosureRep { values, links, kind, id }) =
                (print indent;
                 print "Closure "; pv v; print "/"; pv id;
                 if LV.Set.member (seen, id) then
                   print "(seen)\n"
                 else
                   (print ":\n";
                    case values
                      of [] => ()
                       | _ => (print indent; print "  Vals:"; plist pval values);
                    pclosures ("  " ^ indent, links, LV.Set.add (seen, id))))
          in  app pc l
          end
        fun pcallee (v, StandardContinuation { callee, gpcs, fpcs }) =
             (pv v; print "/"; pval callee; print "(G): "; plist pv gpcs;
              pv v; print "/"; pval callee; print "(F): "; plist pv fpcs)
          | pcallee _ = ()
        fun pproto (v, StandardFunction) = (pv v; print "/std ")
          | pproto (v, StandardContinuation _) = (pv v; print "/cont ")
          | pproto (v, KnownFunction _) = (pv v; print "/known ")
          | pproto (v, MutualRecursion _) = (pv v; print "/recur ")
    in  print "Values:"; plist pv immediates;
        print "Base callee saves:"; plist pv calleeSaves;
        print "Closures:\n"; pclosures ("", closures, LV.Set.empty);
        print "Callee-save registers:\n";
        LV.Map.appi pcallee protocols;
        print "Protocols:\n";
        LV.Map.appi pproto protocols;
        print "\n"
    end

  infix 3 withImms addImms withCSs withClosures withProto
  fun (Env {immediates=_, calleeSaves, closures, protocols, allocated, cg, info})
    withImms imms =
    Env {immediates=imms, calleeSaves=calleeSaves, closures=closures,
         protocols=protocols, allocated=allocated, cg=cg, info=info}
  fun (Env {immediates, calleeSaves, closures, protocols, allocated, cg, info})
    addImms imm =
    Env {immediates=imm@immediates, calleeSaves=calleeSaves, closures=closures,
         protocols=protocols, allocated=allocated, cg=cg, info=info}
  fun (Env {immediates, calleeSaves=_, closures, protocols, allocated, cg, info})
    withCSs calleeSaves =
    Env {immediates=immediates, calleeSaves=calleeSaves, closures=closures,
         protocols=protocols, allocated=allocated, cg=cg, info=info}
  fun (Env {immediates, calleeSaves, closures=_, protocols, allocated, cg, info})
    withClosures closures =
    Env {immediates=immediates, calleeSaves=calleeSaves, closures=closures,
         protocols=protocols, allocated=allocated, cg=cg, info=info}
  fun (Env {immediates, calleeSaves, closures, protocols=_, allocated, cg, info})
    withProto protocols =
    Env {immediates=immediates, calleeSaves=calleeSaves, closures=closures,
         protocols=protocols, allocated=allocated, cg=cg, info=info}

  fun addProtocol (env as Env { protocols, ... }) (f, p) =
    env withProto (LV.Map.insert (protocols, f, p))
  fun recordClosure (env as Env { allocated, ... }) f =
    LV.Tbl.insert allocated (f, Closure)
  fun recordCalleeSave (env as Env { allocated, ... }) f =
    LV.Tbl.insert allocated (f, CalleeSave)
  (* fun (Env {immediates, calleeSaves, closures=_, protocols, cg, info}) *)
  (*   withClosures closures = *)
  (*   Env {immediates=immediates, calleeSaves, closures=closures, *)
  (*        protocols=protocols, cg=cg, info=info} *)
  (* fun (Env {immediates, calleeSaves, closures, protocols=_, cg, info}) *)
  (*   withProtocols protocols = *)
  (*   Env {immediates=immediates, calleeSaves, closures=closures, *)
  (*        protocols=protocols, cg=cg, info=info} *)

  exception ClosureEnv
  (* datatype object = Value of CPS.cty *)
  (*                 | FirstOrder of { label: CPS.lvar, *)
  (*                                   gpfree: CPS.lvar list, *)
  (*                                   fpfree: CPS.lvar list } *)
  (*                 | Closure of closure *)
  (*                 | MutualRecusion of { label: CPS.lvar } *)
  (*                 | Cont of { name: CPS.lvar, *)
  (*                             csg: CPS.lvar list, *)
  (*                             csf: CPS.lvar list } *)
  (* datatype env = Env of { base: CPS.lvar list, *)
  (*                         closures: (CPS.lvar * closure) list, *)
  (*                         what: object LV.Tbl.hash_table } *)

  fun sameLV x y = LV.same (x, y)

  fun whatis (Env {calleeSaves, closures, allocated, cg, ...}) v =
    if List.exists (sameLV v) calleeSaves then
      CG.Value
    else if List.exists (fn (w, _) => LV.same (v, w)) closures then
      CG.Value
    else
      (case LV.Tbl.find allocated v
         of SOME _ => CG.Value
          | NONE   => CG.whatis cg v)

  fun protocolOf (Env {protocols, ...}) v =
    case LV.Map.find (protocols, v)
      of SOME p => p
       | NONE => StandardFunction
           (* FIXME: terrible hack *)
           (* (print (LV.lvarName v ^ " missing protocol in env\n"); *)
           (*        raise ClosureEnv) *)

  fun protocolOf' (Env {protocols, ...}) v = LV.Map.find (protocols, v)

  fun tyOf (Env {info, allocated, ...}) v =
    case LV.Tbl.find allocated v
      of SOME _ => CPSUtil.BOGt
       | NONE   => Syn.typeof info v

  fun requiredVars env v =
    case whatis env v
      of CG.Value => [v]
       | CG.NoBinding => raise Fail "NoBinding requires what?"
       | (CG.FirstOrder _ | CG.Function _) =>
           (case protocolOf env v
              of KnownFunction { gpfree, fpfree, ... } => gpfree @ fpfree
               | MutualRecursion { gpfree, fpfree, ... } => gpfree @ fpfree
               | StandardFunction => [v]
               | StandardContinuation { callee=CPS.VAR f, gpcs, fpcs } =>
                   f::(fpcs @ gpcs)
               | StandardContinuation { callee=_, gpcs, fpcs } => fpcs @ gpcs)

  val isFloatTy =
    if unboxedFloats then
      (fn (CPS.FLTt _) => true | _ => false)
    else
      (fn _ => false)

  fun isUntaggedIntTy (CPS.NUMt {tag, ...}) = not tag
    | isUntaggedIntTy _ = false

  fun isUntaggedInt env = isUntaggedIntTy o (tyOf env)

  fun isFloat env = isFloatTy o (tyOf env)
  fun freevars (Env {info, ...}) = Syn.fv info

  fun collectEnv (env, bindings) =
    let fun unionL (set, xs) = foldl LV.Set.add' set xs
        fun subtractL (set, xs) = foldl LV.Set.subtract' set xs
        fun loop fv =
          let fun collect (v, fv) = unionL (fv, requiredVars env v)
              val fv' = LV.Set.foldl collect LV.Set.empty fv
              val changed = LV.Set.numItems fv <> LV.Set.numItems fv'
          in  if changed then loop fv' else fv'
          end
        val fv = foldl (fn (f, acc) => LV.Set.union (freevars env f, acc))
                       LV.Set.empty
                       bindings
        val fv = subtractL (fv, map #2 bindings)
    in  LV.Set.partition (isFloat env) (loop fv)
    end

  fun dumpLVSet name set =
    print (name ^ ": {"
                ^ String.concatWithMap ", " LV.lvarName (LV.Set.listItems set)
                ^ "}\n")

  fun extraLvar (n, ty) =
    let fun loop (n, args, tys) =
          if n < 1 then
            (List.rev args, tys)
          else
            loop (n - 1, LV.mkLvar ()::args, ty::tys)
    in  loop (n, [], [])
    end

  fun gpType _ = CPSUtil.BOGt
  fun fpType _ = CPS.FLTt 64

  type decision = LCPS.function * protocol * closure list
  type fragment = env * LCPS.function

  datatype fix_kind = UserFix of { knowns: LCPS.function list,
                                   escapes: LCPS.function list }
                    | KnownContFix  of LCPS.function
                    | EscapeContFix of LCPS.function

  fun partitionBindings (bindings : LCPS.function list) : fix_kind =
    case bindings
      of [f as (CPS.KNOWN_CONT, _, _, _, _)] =>
           KnownContFix f
       | [f as (CPS.CONT, _, _, _, _)] =>
           EscapeContFix f
       | []  => raise Fail "empty fix"
       | fs  => let fun isEscape (CPS.ESCAPE, _, _, _, _) = true
                      | isEscape _ = false
                    val (escapes, knowns) = List.partition isEscape bindings
                in  UserFix { knowns = knowns, escapes = escapes }
                end

  fun spill (free, n) =
    if List.length free <= n then
      (free, [])
    else
      List.splitAt (free, n - 1)

  datatype access = Direct | Path of CPS.value * CPS.accesspath
  fun printAccess Direct = print "Direct\n"
    | printAccess (Path (value, path)) =
        let fun pp (CPS.OFFp i) = "." ^ Int.toString i
              | pp (CPS.SELp (i, p)) = "." ^ Int.toString i ^ pp p
        in  case value of CPS.VAR x => print (LV.lvarName x ^ pp path ^ "\n")
               | _ => print "what?\n"
        end

  fun access (env as Env { immediates, calleeSaves, closures, ... }) (CPS.VAR v) =
    let fun loopClosure [] =
              (printEnv env; raise Fail ("Can't find " ^ LV.lvarName v))
          | loopClosure ((clo, ClosureRep { values, ... })::closures) =
              (* FIXME: linked closure *)
              case List.findi (fn (_, CPS.VAR x) => LV.same (x, v) | _ => false)
                              values
                of SOME (i, _) => Path (CPS.VAR clo, CPS.SELp (i, CPS.OFFp 0))
                 | NONE => loopClosure closures
    in  if List.exists (sameLV v) immediates then
          Direct
        else
          loopClosure closures
    end
    | access _ _ = Direct

  fun accessToRecordEl (v, Direct) = (LV.mkLvar (), v, CPS.OFFp 0)
    | accessToRecordEl (v, Path (clo, path)) = (LV.mkLvar (), clo, path)

  fun accessToExp (v, ty, Direct) = (fn x => x)
    | accessToExp (v, ty, Path (clo, path)) =
        let fun follow (CPS.OFFp _, last) exp =
                  raise Fail "following OFFp 0"
              | follow (CPS.SELp (i, CPS.OFFp 0), last) exp =
                  let val this = LV.mkLvar ()
                  in  LCPS.SELECT (LV.mkLvar (), i, last, v, ty, exp)
                  end
              | follow _ _ = raise Fail "not generated"
              (* | follow (CPS.SELp (i, path), last) exp = *)
              (*     let val this = LV.mkLvar () *)
              (*     in  LCPS.SELECT (LV.mkLvar (), i, last, this, CPSUtil.BOGt, follow (path, last) exp) *)
              (*     end *)
        in  follow (path, clo)
        end

  fun accessList (env, args) =
    let fun collect (x' as (CPS.VAR x), hdr) = 
              hdr o accessToExp (x, tyOf env x, access env x')
          | collect (_, hdr) = hdr 
    in  foldl collect (fn x => x) args
    end

  fun fixAppliedArgs (env, xs) =
    let fun collect (CPS.VAR x, (res, hdr)) =
              (case protocolOf' env x
                 of SOME (KnownFunction _) =>
                      raise Fail "this is not a known function"
                  | SOME (StandardContinuation { callee, gpcs, fpcs }) =>
                      let val args = callee :: map CPS.VAR (gpcs @ fpcs)
                          val hdr' = accessList (env, args)
                      in  (args @ res, hdr' o hdr)
                      end
                  | SOME (MutualRecursion { label, gpfree, fpfree }) =>
                      raise Fail "unimp: mutual recursion applied elsewhere"
                  | _ =>
                      let val arg = CPS.VAR x
                          val hdr' = accessList (env, [arg])
                      in  (arg :: res, hdr' o hdr)
                      end)
          | collect (x, (args, hdr)) = (x::args, hdr)
    in  foldr collect ([], fn x => x) xs
        handle ex => (print ("fixAppliedArgs [" ^ String.concatWithMap ", "
        PPCps.value2str xs ^ "]\n"); raise ex)
    end

  fun adjustArgs (env, args, tys) =
    let fun add (arg, CPS.CNTt, (args, tys, env)) =
              let val (csgp, csgpTy) =
                    extraLvar (nGPCalleeSaves, CPSUtil.BOGt)
                  val (csfp, csfpTy) =
                    extraLvar (nFPCalleeSaves, CPS.FLTt 64)
                  val args' = arg :: (csgp @ csfp @ args)
                  val tys'  = CPS.CNTt :: (csgpTy @ csfpTy @ tys)
                  val protocol =
                    StandardContinuation { callee=CPS.VAR arg, gpcs=csgp, fpcs=csfp }
                  val () = app (recordCalleeSave env) (csgp @ csfp)
                  val env' = addProtocol env (arg, protocol)
                  val env' = env' withCSs (csgp @ csfp)
                                  addImms (arg::(csgp @ csfp))
              in  (args', tys', env')
              end
          | add (arg, CPS.FUNt, (args, tys, env)) =
              let val env' = addProtocol env (arg, StandardFunction)
                             addImms [arg]
              in  (arg::args, CPS.FUNt::tys, env')
              end
          | add (arg, ty, (args, tys, env)) =
             (arg::args, ty::tys, env addImms [arg])
    in  ListPair.foldrEq add ([], [], env) (args, tys)
        handle ListPair.UnequalLengths =>
        (print "args="; plength args; print ", tys="; plength tys;
         raise ListPair.UnequalLengths)
    end

  fun makeEnv (env, bindings) : (LCPS.cexp -> LCPS.cexp) * env * fragment list =
    let val () = print "STARTING makeEnv; Environment:\n"
        val () = printEnv env
        val (fpfree, gpfree) = collectEnv (env, bindings)
        val () = (dumpLVSet "fpfree" fpfree; dumpLVSet "gpfree" gpfree)
        val (fpfree, gpfree) = (LV.Set.toList fpfree, LV.Set.toList gpfree)
        val recursives = map #2 bindings
        val fixkind = partitionBindings bindings
        (* val frags = map transform bindings *)
    in  case fixkind
          of KnownContFix (kind, name, args, tys, body) =>
               let val gpfreeTys = map (tyOf env) gpfree
                   val fpfreeTys = map (tyOf env) fpfree
                   val args' = args @ gpfree @ fpfree
                   val tys'  = tys  @ gpfreeTys @ fpfreeTys
                   val (args', tys', env') = adjustArgs (env withImms [], args', tys')
                   val f' = (kind, name, args', tys', body)
                   val protocol =
                     KnownFunction { label=name, gpfree=gpfree, fpfree=fpfree }
                   val nenv = addProtocol env (name, protocol)
                   val nenv = nenv addImms [name]
                   val () = print ("Environment in known-cont "
                                   ^ LV.lvarName name ^ ":\n")
                   val () = printEnv env'
                   val () = print ("Continuing environment:\n")
                   val () = printEnv nenv
               in  (fn x => x, nenv, [(env', f')])
               end
           | EscapeContFix (kind, name, args, tys, body) =>
               let val (utgpfree, gpfree) = List.partition (isUntaggedInt env) gpfree
                   val (gpfree, utrecord) =
                     case utgpfree
                       of [] => (gpfree, NONE)
                        | _  =>
                            let val utrecordvar = LV.mkLvar ()
                                val () = recordClosure env utrecordvar
                                val utrecord =
                                   ClosureRep { values=map CPS.VAR utgpfree,
                                                links=[],
                                                kind=CPS.RK_RAWBLOCK,
                                                id=utrecordvar }
                            in  (utrecordvar :: gpfree, SOME utrecord)
                            end
                   (* FIXME : two spills are different *)
                   val (fpfree, fpspill) = spill (fpfree, nFPCalleeSaves)
                   val (gpfree, fprecord) =
                     case fpspill
                       of [] => (gpfree, NONE)
                        | _  =>
                            let val fprecordvar = LV.mkLvar ()
                                val () = recordClosure env fprecordvar
                                val fprecord =
                                  ClosureRep { values=map CPS.VAR fpfree,
                                               links=[],
                                               kind=CPS.RK_RAW64BLOCK,
                                               id=fprecordvar }
                            in  (fprecordvar :: gpfree, SOME fprecord)
                            end
                   val (gpfree, gpspill) = spill (gpfree, nGPCalleeSaves)
                   val (gpbase, gprecord) =
                     case gpspill
                       of [] => (gpfree, NONE)
                        | _  =>
                            let val gprecordvar = LV.mkLvar ()
                                val () = recordClosure env gprecordvar
                                val gprecord =
                                  ClosureRep { values=map CPS.VAR gpspill,
                                               (*FIXME: fp/utclosures in links*)
                                               links=[],
                                               kind=CPS.RK_CONT,
                                               id=gprecordvar }
                            in  (gprecordvar::gpfree, SOME gprecord)
                            end
                   val cont = LV.mkLvar ()
                   val gpbaseTy = map (tyOf env) gpbase
                   val fpbaseTy = map (tyOf env) fpfree
                   val args' = cont::(gpbase @ fpfree @ args)
                   val tys'  = CPSUtil.BOGt::(gpbaseTy @ fpbaseTy @ tys)
                   (* val (args', tys', env') = adjustArgs (env withImms [], args', tys') *)
                   val env' = env withImms args'
                   fun addClosure (NONE, cls) = cls
                     | addClosure (SOME (cr as ClosureRep { id, ... }), cls) =
                         (id, cr)::cls
                   val closures = foldl addClosure []
                                        [gprecord, fprecord, utrecord]
                   val env'  = env' withCSs      []
                                    withClosures closures
                   val f' = (kind, name, args', tys', body)
                   val () = print ("Environment in escape-cont "
                                   ^ LV.lvarName name ^ ":\n")
                   val () = printEnv env'
                   val protocol = StandardContinuation 
                     { callee=CPS.LABEL name, gpcs=gpbase, fpcs=fpfree }
                   val nenv = addProtocol env (name, protocol)
                   val nenv = nenv addImms [name]
                   fun constructClosure (NONE, (hdr, env')) = (hdr, env')
                     | constructClosure
                       (SOME (ClosureRep { values, links, kind, id }),
                        (hdr, env' as Env { allocated, ... })) =
                         let val recordEls =
                               map (fn v => accessToRecordEl (v, access env' v)) values
                             fun hdr' exp = hdr (LCPS.RECORD (LV.mkLvar(), kind, recordEls, id, exp))
                             val () = LV.Tbl.insert allocated (id, Closure)
                             val env'' = env' addImms [id]
                         in  (hdr', env'')
                         end
                    val (hdr, nenv) = foldl constructClosure (fn x => x, nenv)
                                            [fprecord, utrecord, gprecord]
                   val () = print ("Continuing environment:\n")
                   val () = printEnv nenv
               in  (hdr, nenv, [(env', f')])
               end
           | UserFix { knowns, escapes=[] } =>
               let val gpfreeTys = map (tyOf env) gpfree
                   val fpfreeTys = map (tyOf env) fpfree
                   val recusives = map #2 knowns
                   fun protocol n =
                     MutualRecursion { label=n, gpfree=gpfree, fpfree=fpfree }
                   val env' = foldr
                                (fn (n, env) => addProtocol env (n, protocol n))
                                env recursives
                   fun convert (kind, name, args, tys, body) =
                     let val args' = args @ gpfree @ fpfree
                         val tys'  = tys  @ gpfreeTys @ fpfreeTys
                         val (args', tys', env') = adjustArgs (env' withImms [], args', tys')
                         val f' = (kind, name, args', tys', body)
                         val () = print ("Environment in known "
                                         ^ LV.lvarName name ^ ":\n")
                         val () = printEnv env'
                     in  (env', f')
                     end
                   fun protocol' n =
                     KnownFunction { label=n, gpfree=gpfree, fpfree=fpfree }
                   val nenv = foldr
                                (fn (n, env) => addProtocol env (n, protocol' n))
                                env recursives
                   val nenv = nenv addImms recursives
                   val () = print ("Continuing environment:\n")
                   val () = printEnv nenv
               in  (fn x => x, nenv, map convert knowns)
               end
           | UserFix { knowns=[], escapes } =>
               let val (utgpfree, gpfree) = List.partition (isUntaggedInt env) gpfree
                   val (gpfree, utrecord) =
                     case utgpfree
                       of [] => (gpfree, NONE)
                        | _  =>
                            let val utrecordvar = LV.mkLvar ()
                                val utrecord =
                                   ClosureRep { values=map CPS.VAR utgpfree,
                                                links=[],
                                                kind=CPS.RK_RAWBLOCK,
                                                id=utrecordvar }
                            in  (utrecordvar :: gpfree, SOME utrecord)
                            end
                   (* FIXME : two spills are different *)
                   val (fpfree, fpspill) = spill (fpfree, nFPCalleeSaves)
                   val (gpfree, fprecord) =
                     case fpspill
                       of [] => (gpfree, NONE)
                        | _  =>
                            let val fprecordvar = LV.mkLvar ()
                                val fprecord =
                                  ClosureRep { values=map CPS.VAR fpfree,
                                               links=[],
                                               kind=CPS.RK_RAW64BLOCK,
                                               id=fprecordvar }
                            in  (fprecordvar :: gpfree, SOME fprecord)
                            end
                   val recursives = map #2 escapes
                   val closures =
                     map (fn n =>
                           let val gprecord =
                                 ClosureRep { values=CPS.LABEL n::map CPS.VAR gpfree,
                                              links=[],
                                              kind=CPS.RK_ESCAPE,
                                              id=n }
                           in  gprecord
                           end)
                         recursives
                   fun protocol n =
                     MutualRecursion { label=n, gpfree=[], fpfree=[] }
                   val env' = foldr
                                (fn (n, env) => addProtocol env (n, protocol n))
                                env recursives
                   fun convert ((kind, name, args, tys, body), cr) =
                     let val link = LV.mkLvar ()
                         val clos = LV.mkLvar ()
                         val args' = link::clos::args
                         val tys' = CPSUtil.BOGt::CPSUtil.BOGt::tys
                         val env' = env' withClosures [(clos, cr)]
                         val (args', tys', env') =
                           adjustArgs (env' withImms [], args', tys')
                         val f' = (kind, name, args', tys', body)
                         val () = print ("Environment in escape-fun "
                                         ^ LV.lvarName name ^ ":\n")
                         val () = printEnv env'
                     in  (env', f')
                     end
                   val nenv = foldr
                                (fn (n, env) =>
                                  addProtocol env (n, StandardFunction))
                                env recursives
                   val nenv = nenv addImms recursives
                   fun constructClosure
                       (ClosureRep { values, links, kind, id },
                        (hdr, env' as Env { allocated, ... })) =
                         let val recordEls =
                               map (fn v => accessToRecordEl (v, access env' v)) values
                             fun hdr' exp = hdr (LCPS.RECORD (LV.mkLvar(), kind, recordEls, id, exp))
                             val () = LV.Tbl.insert allocated (id, Closure)
                             val env'' = env' addImms [id]
                         in  (hdr', env'')
                         end
                   val (hdr, nenv) = foldl constructClosure (fn x => x, nenv)
                                           closures
                   val () = print ("Continuing environment:\n")
                   val () = printEnv nenv
               in  (hdr, nenv, ListPair.mapEq convert (escapes, closures))
                   handle ListPair.UnequalLengths =>
                   (print "escapes="; plength escapes; print ", closures=";
                    plength closures;
                    raise ListPair.UnequalLengths)
               end
           | UserFix _ =>
               raise Fail "mixed"
    end

  fun closeFix stagenum (env, f as (kind, name, args, tys, body)) =
        (print ("converting fragment: " ^ LV.lvarName name ^ "\n");
         printCPS f;
         (kind, name, args, tys, close (env, stagenum, body)))
         handle e => (print ("In function " ^ LV.lvarName name ^ "\n"); raise e)
  and close (env, stagenum, cexp) =
        case cexp
          of LCPS.FIX (label, bindings, e) =>
               let val (hdr, nenv, frags) = makeEnv (env, bindings)
                   val () = print "END makeEnv\n"
               in  LCPS.FIX (label,
                             map (closeFix stagenum) frags,
                             hdr (close (nenv, stagenum, e)))
               end
           | LCPS.APP (label, CPS.VAR f, args) =>
               (case protocolOf env f
                  of KnownFunction { label, gpfree, fpfree } =>
                       let val f' = CPS.LABEL label
                           val args' = args @ map CPS.VAR (gpfree @ fpfree)
                           val (args', hdr) = fixAppliedArgs (env, args')
                       in  hdr (LCPS.APP (LV.mkLvar(), CPS.LABEL label, args'))
                       end
                   | MutualRecursion { label, gpfree, fpfree } =>
                       let val f' = CPS.LABEL label
                           val args' = args @ map CPS.VAR (gpfree @ fpfree)
                           val (args', hdr) = fixAppliedArgs (env, args')
                       in  hdr (LCPS.APP (LV.mkLvar(), CPS.LABEL label, args'))
                       end
                   | StandardFunction =>
                       let val f' = CPS.VAR f
                           val hdr1 = accessList (env, [f'])
                           val (args', hdr2) = fixAppliedArgs (env, args)
                           val hdr = hdr1 o hdr2
                           val l = LV.mkLvar ()
                       in  hdr (LCPS.SELECT (LV.mkLvar(), 0, f', l, CPS.FUNt,
                                  LCPS.APP (LV.mkLvar(), CPS.VAR l,
                                    (CPS.VAR l)::f'::args')))
                       end
                   | StandardContinuation { callee, gpcs, fpcs } =>
                       let val f' = callee
                           val args = map CPS.VAR (gpcs @ fpcs) @ args
                           val hdr  = accessList (env, args)
                       in  hdr (LCPS.APP (LV.mkLvar(), f', f' :: args))
                       end)
           | LCPS.APP (label, _, args) => raise Fail "call???"
           | LCPS.RECORD (label, rk, elems, name, e) =>
               let val hdr = accessList (env, map #2 elems)
                   val env' = env addImms [name]
               in  hdr (LCPS.RECORD (label, rk, elems, name,
                                     close (env', stagenum, e)))
               end
           | LCPS.SELECT (label, n, v, x, ty, e) =>
               let val hdr = accessList (env, [v])
                   val env' = env addImms [x]
               in  hdr (LCPS.SELECT (label, n, v, x, ty,
                                     close (env', stagenum, e)))
               end
           | LCPS.OFFSET _ => raise Fail "offset"
           | LCPS.SWITCH (label, v, x, branches) =>
               let val hdr = accessList (env, [v])
               in  hdr (LCPS.SWITCH (label, v, x,
                          map (fn e => close (env, stagenum, e)) branches))
               end
           | LCPS.BRANCH (label, b, args, x, con, alt) =>
               let val hdr = accessList (env, args)
               in  hdr (LCPS.BRANCH (label, b, args, x, 
                          close (env, stagenum, con),
                          close (env, stagenum, alt)))
               end
           | LCPS.SETTER (label, s, args, e) =>
               let val hdr = accessList (env, args)
               in  hdr (LCPS.SETTER (label, s, args, close (env, stagenum, e)))
               end
           | LCPS.LOOKER (label, l, args, x, ty, e) =>
               let val hdr = accessList (env, args)
                   val env' = env addImms [x]
                   val e' = close (env', stagenum, e)
               in  hdr (LCPS.LOOKER (label, l, args, x, ty, e'))
               end
           | LCPS.ARITH (label, a, args, x, ty, e) =>
               let val hdr = accessList (env, args)
                   val env' = env addImms [x]
                   val e' = close (env', stagenum, e)
               in  hdr (LCPS.ARITH (label, a, args, x, ty, e'))
               end
           | LCPS.PURE (label, p, args, x, ty, e) =>
               let val hdr = accessList (env, args)
                   val env' = env addImms [x]
                   val e' = close (env', stagenum, e)
               in  hdr (LCPS.PURE (label, p, args, x, ty, e'))
               end
           | LCPS.RCC (l, b, name, ty, args, res, e) =>
               let val hdr = accessList (env, args)
                   val env' = raise Fail "TODO"
                   val e' = close (env', stagenum, e)
               in  hdr (LCPS.RCC (l, b, name, ty, args, res, e'))
               end

  fun closeCPS ((kind, name, args, tys, body), cg, info, stagenum) =
    let val initEnv =
          Env { immediates=[], calleeSaves=[], closures=[],
                protocols=LV.Map.singleton (name, StandardFunction),
                allocated=LV.Tbl.mkTable (32, ClosureEnv), cg=cg, info=info }
        val (link, clos) = (LV.mkLvar (), LV.mkLvar ())
        val args' = link::clos::args
        val tys'  = CPSUtil.BOGt::CPSUtil.BOGt::tys
        val (args', tys', env') = adjustArgs (initEnv, args', tys')
    in  closeFix stagenum (env', (kind, name, args', tys', body))
    end

  fun convert (cps, cg, info)  =
    let
      val cps = assignFunKind (cps, cg, info)
      (* val () = (print ">>>after fk\n"; PPCps.printcps0 (LCPS.unlabelF cps); *)
      (*           print "<<<after fk\n") *)
      val sn = installStageNumbers (cps, cg, info)
      val () = dumpStageNumbers sn
      val cps = closeCPS (cps, cg, info, sn)
      val () = print ">>>>>>>>>>>>>>>>>> AFTER <<<<<<<<<<<<<<<<<<<<\n"
      val () = printCPS cps
      val () = print ">>>>>>>>>>>>>>>>>>  END  <<<<<<<<<<<<<<<<<<<<\n"
    in
      cps
    end
end
