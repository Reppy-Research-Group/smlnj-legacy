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
  val printExp = PPCps.prcps o LCPS.unlabel

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
           | CG.Unreachable => (print ("unreachable: " ^ LV.lvarName name ^ "\n");
                                false)
    end

  fun tagInt i = CPS.NUM { ival = IntInf.fromInt i,
                           ty = { sz=Target.defaultIntSz, tag=true }}

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
              (CPS.KNOWN, name, args, tys, fixE body)
              (* let val fv = Syn.fv info f *)
              (* in  if List.exists (fn r => LV.Set.member (fv, r)) recs then *)
              (*       (1* (CPS.KNOWN_REC, name, args, tys, fixE body) *1) *)
              (*       (CPS.KNOWN, name, args, tys, fixE body) *)
              (*     else *)
              (*       (CPS.KNOWN, name, args, tys, fixE body) *)
              (* end *)
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
      (* fun assign (CG.Single f) = *)
      (*       insert (f, maxSNOfPred f + 1) *)
      (*   | assign (CG.Group fs) = *)
      (*       let val maxSN = maxMap maxSNOfPred fs *)
      (*           val sn = maxSN + 1 *)
      (*       in  app (fn f => insert (f, sn)) fs *)
      (*       end *)
      fun assign (CG.Single f, i) =
            (insert (f, i); i + 1)
        | assign (CG.Group fs, i) =
            (app (fn f => insert (f, i)) fs; i + 1)
    in
      foldl assign 0 components;
      snTbl
    end

  fun calculateFreeInEscape (cg, info) =
    let val isFO = isFirstOrder (cg, info)
        fun fv x = Syn.fv info x
                   handle e => (print ("missing " ^ LV.lvarName (#2 x) ^ " in syntatic"); raise e)
        fun collect (f, set) = if isFO f then set else LV.Set.union (set, fv f)
        val set = Vector.foldl collect LV.Set.empty (CG.allFunctions cg)
    in  fn (f: LCPS.function) => LV.Set.member (set, #2 f)
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
  datatype protocol = KnownFunction of { label: CPS.lvar, pvd: CPS.lvar list }
                    | Recursion     of { label: CPS.lvar, pvd: CPS.lvar list }
                    | StandardFunction
                    | StandardContinuation of { callee: CPS.value,
                                                gpcs: CPS.value list,
                                                fpcs: CPS.value list }
  datatype object = Closure | CalleeSave
  datatype env = Env of { immediates: CPS.lvar list,
                          calleeSaves: CPS.lvar list,
                          closures: (CPS.lvar * closure) list,
                          (* facts *)
                          protocols: protocol LV.Map.map,
                          allocated: object LV.Tbl.hash_table,
                          cg: CG.t,
                          info: Syn.t }
  fun closureID (ClosureRep {id, ...}) = id

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
             (pv v; print "/"; pval callee; print "(G): "; plist pval gpcs;
              pv v; print "/"; pval callee; print "(F): "; plist pval fpcs)
          | pcallee _ = ()
        fun pproto (v, StandardFunction) = (pv v; print "/std "; print "\n")
          | pproto (v, StandardContinuation _) = (pv v; print "/cont\n")
          | pproto (v, KnownFunction {label, pvd}) =
             (pv v; print "/known/"; pv label; print ": "; plist pv pvd)
          | pproto (v, Recursion {label, pvd}) = 
             (pv v; print "/recur/"; pv label; print ": "; plist pv pvd)
    in  print "Values:"; plist pv immediates;
        print "Base callee saves:"; plist pv calleeSaves;
        print "Closures:\n"; pclosures ("", closures, LV.Set.empty);
        print "Callee-save registers:\n";
        LV.Map.appi pcallee protocols;
        print "Protocols:\n";
        LV.Map.appi pproto protocols;
        print "\n"
    end

  infix 3 withImms addImms withCSs withClosures addClosure withProto
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
  fun (Env {immediates, calleeSaves, closures, protocols, allocated, cg, info})
    addClosure clo =
    Env {immediates=immediates, calleeSaves=calleeSaves,
         closures=clo::closures,
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

  fun lookupClosure (Env { closures, ... }, v) : closure =
    case List.find (fn (n, _) => LV.same (n, v)) closures
      of SOME (_, clo) => clo
       | NONE => raise Fail ("lookupClosure: " ^ LV.lvarName v
                                               ^ " is not in closure")

  fun protocolOf (Env {protocols, ...}) v =
    case LV.Map.find (protocols, v)
      of SOME p => p
       | NONE => StandardFunction
           (* FIXME: terrible hack *)
           (* (print (LV.lvarName v ^ " missing protocol in env\n"); *)
           (*        raise ClosureEnv) *)

  fun protocolOf' (Env {protocols, ...}) v = LV.Map.find (protocols, v)

  fun ctyOfClo (ClosureRep { values, links, ... }): CPS.cty =
    let val length = List.length values + List.length links
    in  CPS.PTRt (CPS.RPT length)
    end

  fun tyOf (Env {info, allocated, closures, ...}) v =
    case LV.Tbl.find allocated v
      of SOME _ => CPSUtil.BOGt
       | NONE   =>
           (case List.find (fn (name, clo) => LV.same (name, v)) closures
              of SOME (_, clo) => ctyOfClo clo
               | NONE =>
                   Syn.typeof info v
                   handle Syn.SyntacticInfo =>
                   (print (LV.lvarName v ^ " missing in syntactic");
                    raise Syn.SyntacticInfo))

  fun varsInValue ls =
    let fun g ([], result) = result
          | g (CPS.VAR x :: xs, result) = g (xs, x::result)
          | g (_::xs, result) = g (xs, result)
    in  g (ls, [])
    end

  fun requiredVars env v =
    case whatis env v
      of CG.Value => [v]
       (* | CG.NoBinding => (1* FIXME: what does NoBinding requre? *1) *)
           (* raise Fail ("NoBinding " ^ LV.lvarName v ^ " requires what?") *)
       | (CG.FirstOrder _ | CG.Function _ | CG.NoBinding) =>
           (case protocolOf env v
              of KnownFunction { pvd, ... } => pvd
               | Recursion { pvd, ... } => pvd
               | StandardFunction => [v]
               | StandardContinuation { callee, gpcs, fpcs } =>
                   varsInValue (callee::(fpcs @ gpcs)))

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
    in  loop fv
    end

  fun dumpLVList name set =
    print (name ^ ": {"
                ^ String.concatWithMap ", " LV.lvarName set
                ^ "}\n")
  fun dumpLVSet name set = dumpLVList name (LV.Set.listItems set)

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

  datatype fix_kind = SimpleKnownFix of LCPS.function
                    | EscapeUserFix  of LCPS.function
                    | EscapeContFix  of LCPS.function
                    | MutualRecursionFix of {
                        known:  LCPS.function list,
                        escape: LCPS.function list
                      }

  fun partitionBindings (bindings : LCPS.function list) : fix_kind =
    case bindings
      of [f as (CPS.KNOWN_CONT, _, _, _, _)] =>
           SimpleKnownFix f
       | [f as (CPS.CONT, _, _, _, _)] =>
           EscapeContFix f
       | fs  => let fun isEscape (CPS.ESCAPE, _, _, _, _) = true
                      | isEscape _ = false
                in  case List.partition isEscape bindings
                      of ([], [])  => raise Fail "empty fix"
                       | ([], [f]) => SimpleKnownFix f
                       | ([f], []) => EscapeUserFix f
                       | (escape, known) =>
                           MutualRecursionFix { known=known, escape=escape }
                end

  fun spill (free, n) =
    if List.length free <= n then
      (free, [])
    else
      List.splitAt (free, n - 1)

  datatype access = Direct | Indirect of CPS.lvar * closure * path
       and path   = Last of CPS.lvar | Select of CPS.lvar * path

  fun printAccess Direct = print "direct\n"
    | printAccess (Indirect (name, _, path)) =
        let fun ppath (Last field) = print ("." ^ LV.lvarName field)
              | ppath (Select (field, path)) =
                  (print ("." ^ LV.lvarName field); ppath path)
        in  print (LV.lvarName name); ppath path
        end

  fun access (env as Env { immediates, closures, ... }) v =
    let fun next (path : path -> access, links) =
          map (fn (_, clo) => (fn p => path (Select (closureID clo, p)), clo)) links
        fun init (name, clo) = (fn p => Indirect (name, clo, p), clo)
        fun sameValue (CPS.VAR w)   = LV.same (v, w)
          | sameValue (CPS.LABEL w) = LV.same (v, w)
              andalso (print ("looking for label? " ^ LV.lvarName w ^ "\n");
                       printEnv env;
                       true)
          | sameValue _ = false
        fun sameClosure (_, cl) = LV.same (v, closureID cl)
        fun bfs ([], seen) =
              (printEnv env; raise Fail ("Can't find " ^ LV.lvarName v))
          | bfs ((path, ClosureRep { values, links, id, ... })::todo, seen) =
              if LV.Set.member (seen, id) then
                bfs (todo, seen)
              else if List.exists sameClosure links then
                path (Last v)
              else if List.exists sameValue values then
                path (Last v)
              else
                bfs (todo @ next (path, links), LV.Set.add (seen, id))
    in  if List.exists (sameLV v) immediates then
          Direct
        else
          bfs (map init closures, LV.Set.empty)
    end

  (* val access = fn env => fn v => *)
  (*   let val res = access env v *)
  (*   in  print (concat ["Access ", LV.lvarName v, ": "]); *)
  (*       printAccess res; *)
  (*       print "\n"; *)
  (*       res *)
  (*   end *)

  fun offsetOf (ClosureRep { values, links, ... }, v) : int * closure option =
    case List.findi (fn (_, (CPS.VAR x | CPS.LABEL x)) => LV.same (x, v)
                      | _ => false) values
      of SOME (off, _) => (off, NONE)
       | NONE =>
           let val off = List.length values
           in  case List.findi (fn (_, (_, cl)) => LV.same (closureID cl, v)) links
                 of SOME (i, (_, clo)) => (off + i, SOME clo)
                  | NONE => raise Fail ("offsetOf: " ^ LV.lvarName v
                                                     ^ " not in closure")
           end

  val offsetOfVal = #1 o offsetOf
  fun offsetOfClo (clo, v) =
    let val (off, closureOpt) = offsetOf (clo, v)
                  handle e => raise e
    in  case closureOpt
          of NONE => raise Fail (LV.lvarName v ^ " is not a closure")
           | SOME closure => (off, closure)
    end

  fun accessToRecordEl (v, Direct) = (LV.mkLvar (), v, CPS.OFFp 0)
    | accessToRecordEl (v, Indirect (n, clo, path)) =
        let fun pathToAP (clo, Last v) : CPS.accesspath =
                 (CPS.SELp (offsetOfVal (clo, v), CPS.OFFp 0)
                  handle e => raise e)
              | pathToAP (clo, Select (field, path)) =
                  let val (off, closure) = offsetOfClo (clo, field)
                  handle e => raise e
                  in  CPS.SELp (off, pathToAP (closure, path))
                  end
        in  (LV.mkLvar (), CPS.VAR n, pathToAP (clo, path))
        end

  fun emitAccess _   (_,  _, Direct) = (fn exp => exp)
    | emitAccess env (v, ty, Indirect (name, closure, path)) =
        let fun follow (name, closure, Last n) exp =
                  (LCPS.SELECT (LV.mkLvar (),
                    offsetOfVal (closure, n), CPS.VAR name, v, ty, exp)
    handle e => (print ("access " ^ LV.lvarName v ^ ": ");
                 printEnv env;
                 printAccess (Indirect (name, closure, path)); raise e))
              | follow (name, closure, Select (field, path)) exp =
                  let val (off, next) = offsetOfClo (closure, field)
                  handle e => raise e
                      val nextName = LV.mkLvar ()
                  in  LCPS.SELECT (LV.mkLvar (),
                        off, CPS.VAR name, nextName, ctyOfClo next,
                        follow (nextName, next, path) exp)
                  end
        in  follow (name, closure, path)
        end

  val accessToRecordEl = fn (v, access) =>
    (accessToRecordEl (v, access)
    handle e => (print ("access " ^ PPCps.value2str v ^ ": ");
                 printAccess access; print"\n"; raise e))

  val emitAccess = fn env => fn (v, ty, access) =>
    (emitAccess env (v, ty, access)
    handle e => (print ("access " ^ LV.lvarName v ^ ": ");
                 printAccess access; printEnv env; raise e))

  fun fixRecordEl (env, CPS.VAR v) = (accessToRecordEl (CPS.VAR v, access env v)
                                      handle e => (printEnv env; raise e))
    | fixRecordEl (_, v) = (LV.mkLvar (), v, CPS.OFFp 0)

  fun fixAccess (env, args) =
    let fun collect (CPS.VAR x, hdr) exp =
              hdr (emitAccess env (x, tyOf env x, access env x) exp)
          | collect (_, hdr) exp = hdr exp
    in  foldl collect (fn x => x) args
        handle ex => (print ("fixAccess [" ^ String.concatWithMap ", "
        PPCps.value2str args ^ "]\n"); raise ex)
    end

  fun emitClosure (env, ClosureRep {kind, values, links, id}) =
    let val linkVs = map (CPS.VAR o #1) links
        val fields = values @ linkVs
        val recordEls = map (fn v => fixRecordEl (env, v)) fields
    in  fn cexp => LCPS.RECORD (LV.mkLvar(), kind, recordEls, id, cexp)
    end

  type header = LCPS.cexp -> LCPS.cexp

  fun fixActualArgs (env, xs) =
    let fun collect (CPS.VAR x, (res, hdr)) =
              (case protocolOf' env x
                 of SOME (KnownFunction _) =>
                      raise Fail "this is not a known function"
                  | SOME (StandardContinuation { callee, gpcs, fpcs }) =>
                      let val args = callee :: (gpcs @ fpcs)
                          val hdr' = fixAccess (env, args)
                      in  (args @ res, hdr' o hdr)
                      end
                  | SOME (Recursion { label, pvd }) =>
                      (* let val hdr' = emitClosure (env, ClosureRep { *)
                      (*                   kind=CPS.RK_ESCAPE, *)
                      (*                   values=CPS.LABEL label::map CPS.VAR pvd, *)
                      (*                   links=[], *)
                      (*                   id=x}) *)
                      (* in  (CPS.VAR x :: res, hdr' o hdr) *)
                      (* end *)
                      raise Fail "unimp: mutual recursion applied elsewhere"
                  | _ =>
                      let val arg = CPS.VAR x
                          val hdr' = fixAccess (env, [arg])
                      in  (arg :: res, hdr' o hdr)
                      end)
          | collect (x, (args, hdr)) = (x::args, hdr)
    in  foldr collect ([], fn x => x) xs
        handle ex => (print ("fixAppliedArgs [" ^ String.concatWithMap ", "
        PPCps.value2str xs ^ "]\n"); raise ex)
    end

  fun adjustFormalArgs (env, args, tys) =
    let fun add (arg, CPS.CNTt, (args, tys, env)) =
              let val (csgp, csgpTy) =
                    extraLvar (nGPCalleeSaves, CPSUtil.BOGt)
                  val (csfp, csfpTy) =
                    extraLvar (nFPCalleeSaves, CPS.FLTt 64)
                  val args' = arg :: (csgp @ csfp @ args)
                  val tys'  = CPS.CNTt :: (csgpTy @ csfpTy @ tys)
                  val protocol =
                    StandardContinuation { callee=CPS.VAR arg, gpcs=map CPS.VAR
                    csgp, fpcs=map CPS.VAR csfp }
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

  datatype either = datatype Either.either

  type slot = (CPS.lvar, closure) either

  fun fetchAllClosures (Env { closures, ... }) : closure list =
    let fun collect ((v, clo as ClosureRep {id, links, ...}), (seen, clos)) =
          if LV.Set.member (seen, id) then
            (seen, clos)
          else
            foldl collect (LV.Set.add (seen, id), clo :: clos) links
    in  #2 (foldl collect (LV.Set.empty, []) closures)
    end

  fun closureSharing (env, vars) : slot list =
    (* FIXME: Many O(n^2) iterations, consider using sets *)
    (* FIXME: sharing a closure for one variable is not worth it *)
    let val closures = fetchAllClosures env
        fun isShareable (ClosureRep {values, kind, ...}) =
          let fun existsInVars (CPS.VAR v) = List.exists (sameLV v) vars
                | existsInVars _ = true (* extra labels in closure is safe *)
          in  case kind
                of (CPS.RK_RAWBLOCK | CPS.RK_RAW64BLOCK) => true
                 | _ => List.all existsInVars values
          end
        val shareableClosures = List.filter isShareable closures
        fun cmpSize (ClosureRep {values=v1, ...}, ClosureRep {values=v2, ...}) =
          List.length v1 < List.length v2
        val shareableClosures = ListMergeSort.sort cmpSize shareableClosures
        fun replace ([], _, slots) = slots
          | replace (vars, [], slots) = map INL vars @ slots
          | replace (vars, (clo as ClosureRep {values, id, ...})::todo, slots) =
              let fun inClosure v =
                    LV.same (v, id)
                    orelse
                    List.exists (fn (CPS.VAR w | CPS.LABEL w) => LV.same (v, w)
                                  | _ => false) values
                  val (replaced, remaining) = List.partition inClosure vars
              in  case replaced
                    of [] => replace (remaining, todo, slots)
                     | _  => replace (remaining, todo, INR clo :: slots)
              end
    in  replace (vars, shareableClosures, [])
    end

  fun printSlots slots =
    print (concat ["[", String.concatWithMap ", "
                          (fn INL v => "(V)" ^ LV.lvarName v
                            | INR c => "(C)" ^ LV.lvarName (closureID c))
                          slots, "]"])

  (* val closureSharing = fn (env, vars) => *)
  (*   let val res = closureSharing (env, vars) *)
  (*   in  print "CLOSURE SHARING:\n"; *)
  (*       printEnv env; *)
  (*       print "\nvars: "; dumpLVList "" vars; *)
  (*       print "slots:"; printSlots res; *)
  (*       print "\n\n"; *)
  (*       res *)
  (*   end *)

  fun mkClosure (vars, links, kind) : closure =
    let val var = LV.mkLvar ()
    in  ClosureRep { values=map CPS.VAR vars,
                     links=map (fn l => (closureID l, l)) links,
                     kind=kind,
                     id=var }
    end

  fun mkClosureOpt ([], [], _) = NONE
    | mkClosureOpt (v, l, k) = SOME (mkClosure (v, l, k))

  fun flattenOpt ls = List.mapPartial (fn x => x) ls
  val _ = flattenOpt : 'a option list -> 'a list

  fun spill (n: int, raw: slot -> bool, slots: slot list)
    : slot list * slot list =
    (* FIXME when lut and fut is figured out *)
    let val (raws, slots) = List.partition raw slots
        (* val () = (print "raws: "; printSlots raws; print "\n") *)
        (* val () = (print "slots: "; printSlots slots; print "\n") *)
    in if List.length slots <= n andalso List.length raws = 0 then
         (slots, [])
       else
         let val (vars, links) = Either.partition slots
             fun fill (0, vs, ls, slots) =
                   (slots, map INL vs @ map INR ls @ raws)
               | fill (n, vs, l::ls, slots) =
                   fill (n - 1, vs, ls, INR l :: slots)
               | fill (n, v::vs, [], slots) =
                   fill (n - 1, vs, [], INL v :: slots)
               | fill (n, [], [], slots) = (slots, raws)
         in  fill (n - 1, vars, links, [])
         end
    end

  fun closureName (Env {closures, ...}, ClosureRep {id, ...}) =
    let fun alias (name, ClosureRep {id=id2, ...}) = LV.same (id, id2)
    in  case List.find alias closures
          of SOME (name, _) => name
           | NONE => id
    end

  fun layout (build: CPS.value list * closure list -> closure)
             (env, slots: slot list) : (closure * header) option =
    let val (vars, clos)   = Either.partition slots
        val (fpvars, vars) = List.partition (isFloat env) vars
        val (utvars, vars) = List.partition (isUntaggedInt env) vars
        (* TODO: Merge two blocks *)
        val fpclosure = mkClosureOpt (fpvars, [], CPS.RK_RAW64BLOCK)
        val utclosure = mkClosureOpt (utvars, [], CPS.RK_RAWBLOCK)
        val newClos = flattenOpt [fpclosure, utclosure]
    in  case (vars, clos @ newClos)
          of ([], []) => NONE
           | (vars, links) =>
               let val clos = build (map CPS.VAR vars, links)
                   val newNames = map closureID newClos
                   val env = env addImms newNames
                             before (app (recordClosure env) newNames)
                   fun prepend (clos, hdr') = emitClosure (env, clos) o hdr'
                   val hdr' = foldl prepend (emitClosure (env, clos)) newClos
               in  SOME (clos, hdr')
               end
    end

  fun getSingleton [x] = x
    | getSingleton _   = raise Fail "getSingleton"

  val vl = CPS.VAR : CPS.lvar -> CPS.value

  fun addPvdToArgs (env, args, tys, pvd) =
    let fun collect (INL v, (vs, ts, env)) =
              (vs @ [v], ts @ [tyOf env v], env addImms [v])
          | collect (INR c, (vs, ts, env)) =
              let val name = closureID c
              in  (vs @ [name], ts @ [ctyOfClo c],
                   env addClosure (name, c) addImms [name])
              end
    in  foldl collect (args, tys, env) pvd
    end
  fun nameOfSlots pvd = map (fn INL v => v | INR c => closureID c) pvd

  fun fill (env, n, slots) : CPS.lvar list * CPS.cty list * CPS.value list =
    let fun go (0, [], vs, tys, vls) = (List.rev vs, List.rev tys, List.rev vls)
          | go (0, _ , _, _, _) =
              (printSlots slots; raise Fail "len(slots) >= n")
          | go (n, [], vs, tys, vls) =
              go (n - 1, [], LV.mkLvar ()::vs, gpType ()::tys, tagInt 0::vls)
          | go (n, (INL v)::slots, vs, tys, vls) =
              go (n - 1, slots, v::vs, tyOf env v::tys, CPS.VAR v::vls)
          | go (n, (INR c)::slots, vs, tys, vls) =
              let val name = closureName (env, c)
              in  go (n - 1, slots, name::vs, ctyOfClo c::tys, CPS.VAR name::vls)
              end
    in  go (n, slots, [], [], [])
    end

  fun mklinks (env, closures) = map (fn c => (closureName (env, c), c)) closures
  fun isRaw env (INL v) = isFloat env v orelse isUntaggedInt env v
    | isRaw env (INR _) = false

  fun makeEnv (env, (sn, freeInEscape), fs): header * env * fragment list =
    case partitionBindings fs
      of SimpleKnownFix (f as (_, name, args, tys, body)) =>
           let val fv = LV.Set.toList (collectEnv (env, [f]))
               (* val () = (dumpLVList "fv" fv) *)
               val (pvd, hdr, env) =
                 if freeInEscape f then
                   let val slots = closureSharing (env, fv)
                       val (slot, spilled) = spill (1, isRaw env, slots)
                       (* val () = (print "slots: "; printSlots slots; print "\n") *)
                       (* val () = (print "spilled: "; printSlots spilled; print "\n") *)
                       fun emit (vals, links) =
                         ClosureRep { values=vals, links=mklinks (env, links),
                                      kind=CPS.RK_KNOWN, id=LV.mkLvar() }
                   in  case layout emit (env, spilled)
                         of NONE => (slots, fn x => x, env)
                          | SOME (clos, hdr) =>
                              let val name = closureName (env, clos)
                              in  ([INR clos], hdr,
                                   (env addImms [name] addClosure (name, clos))
                                    before (recordClosure env name))
                              end
                   end
                 else
                   (map INL fv, fn x => x, env)
               val pvdVars = nameOfSlots pvd
               val nenv = env withImms pvdVars withClosures []
               val (args', tys', nenv) = adjustFormalArgs (nenv, args, tys)
               (* val () = (dumpLVList "args before" args') *)
               val (args', tys', nenv) = addPvdToArgs (nenv, args', tys', pvd)
               (* val () = (dumpLVList "args after" args') *)
               (* val () = (dumpLVList "pvdVars" pvdVars) *)
               val nenv = addProtocol nenv
                            (name, Recursion { label=name, pvd=pvdVars } )
               val env' = env addImms [name]
               val env' = addProtocol env'
                            (name, KnownFunction { label=name, pvd=pvdVars })
           in  (hdr, env', [(nenv, (CPS.KNOWN, name, args', tys', body))])
           end
       | EscapeUserFix (f as (kind, name, args, tys, body)) =>
           let val fv = LV.Set.toList (collectEnv (env, [f]))
               val slots = closureSharing (env, fv)
               fun emit (vals, links) =
                 ClosureRep { values=CPS.LABEL name::vals,
                              links=mklinks (env, links),
                              kind=CPS.RK_ESCAPE, id=name }
               val nenv = env withImms [] withClosures []
               val env' = env addImms [name]
               val env' = addProtocol env' (name, StandardFunction)
               (* val (link, clos) = (LV.mkLvar (), LV.mkLvar ()) *)
               val (link, clos) = (LV.mkLvar (), name)
           in  case layout emit (env, slots)
                 of NONE => (* f doesn't need an environment *)
                      let val args' = link::clos::args
                          val tys'  = CPSUtil.BOGt::CPSUtil.BOGt::tys
                          val nenv = addProtocol nenv (name,
                                       Recursion { label=name, pvd=[] })
                          val (args', tys', nenv) =
                            adjustFormalArgs (nenv, args', tys')
                          val hdr = emitClosure
                            (env, ClosureRep { kind=CPS.RK_ESCAPE,
                                               values=[CPS.LABEL name],
                                               links=[], id=name })
                      in  (hdr, env', [(nenv, (kind, name, args', tys', body))])
                      end
                  | SOME (closure, hdr) =>
                      let val args' = link::clos::args
                          val tys'  = CPSUtil.BOGt::ctyOfClo closure::tys
                          val nenv = addProtocol nenv (name,
                                       Recursion { label=name, pvd=nameOfSlots
                                       slots })
                          val (args', tys', nenv) =
                            adjustFormalArgs (nenv, args', tys')
                          val nenv = nenv addClosure (clos, closure)
                          val env' = env' addClosure (name, closure)
                      in  recordClosure env' name;
                          (hdr, env', [(nenv, (kind, name, args', tys', body))])
                      end
           end
       | EscapeContFix (f as (kind, name, args, tys, body)) =>
           let val fv = LV.Set.toList (collectEnv (env, [f]))
               (* val () = (print (LV.lvarName name ^ ": "); dumpLVList "fv" fv) *)
               val slots = closureSharing (env, fv)
               (* val () = (print ("after sharing: "); printSlots slots) *)
               (* val (raw, slots) = List.partition isRaw slots *)
               (* FIXME: kick floats out of slots *)
               val (slots, spilled) = spill (nGPCalleeSaves, isRaw env, slots)
               (* val spilled = spilled @ raw *)
               (* val () = (print ("\nspilled: "); printSlots spilled) *)
               (* val () = (print ("\nslots: "); printSlots slots) *)
               fun emit (vals, links) =
                 ClosureRep { values=vals, links=mklinks (env, links),
                              kind=CPS.RK_CONT, id=LV.mkLvar () }
               val (cs, hdr, env) =
                 case layout emit (env, spilled)
                   of NONE => (slots, fn x => x, env)
                    | SOME (clos, hdr) =>
                        let val name = closureID clos
                        in  (INR clos :: slots, hdr,
                             env addImms [name] before (recordClosure env name))
                        end
               val nenv = env withImms [] withClosures [] withCSs []
               val nenv = foldl (fn (INL v, nenv) => nenv addImms [v]
                                  | (INR c, nenv) =>
                                      let val name = closureName (env, c)
                                      in  nenv addImms [name]
                                               addClosure (name, c)
                                      end)
                                nenv cs
               val (csargs, cstys, csvalues) = fill (env, nGPCalleeSaves, cs)
               val (args', tys', nenv) = adjustFormalArgs (nenv, args, tys)
               val link = LV.mkLvar ()
               val args' = link :: csargs @ args'
               val tys'  = CPSUtil.BOGt :: cstys @ tys'
               val nenv  = nenv addImms csargs
               val env' = env addImms [name]
               val env' = addProtocol env
                 (name, StandardContinuation
                          { callee=CPS.LABEL name, gpcs=csvalues, fpcs=[] })
           in  (hdr, env', [(nenv, (kind, name, args', tys', body))])
           end
       | MutualRecursionFix { known, escape } =>
           (* FIXME: currently not taking advantage of known mut rec functions
            *)
           raise Fail "unimp"
           (* let val fv = LV.Set.toList (collectEnv (env, fs)) *)
           (*     val slots = closureSharing (env, fv) *)
           (*     fun emit (vals, links) = *)
           (*       ClosureRep { values=vals, links=links, *)
           (*                    kind=CPS.RK_ESCAPE, id=LV.mkLvar () } *)
           (*     fun rkkind CPS.ESCAPE = CPS.RK_ESCAPE *)
           (*       | rkkind _ = CPS.RK_KNOWN *)
           (*     fun mkShared NONE (f as (kind, name, _, _, _) = *)
           (*           ClosureRep { values=[CPS.LABEL name], links=[], *)
           (*                        kind=rkkind kind, id=name } *)
           (*       | mkShared (SOME closure) (f as (kind, name, _, _, _)) = *)
           (*           ClosureRep { values=[CPS.LABEL name], *)
           (*                        links=[(closureID closure, closure)], *)
           (*                        kind=rkkind kind, id=name } *)
           (*     val nenv = env withImms [] withClosures [] *)
           (*     val (pvd, hdr, closure) = *)
           (*       case layout emit (env, slots) *)
           (*         of NONE => ([], fn x => x, NONE) *)
           (*          | SOME (c, hdr) => ([closureID c], hdr, SOME c) *)
           (*     val escapeClos = map (mkShared NONE) escape *)
           (*     val hdr = foldr (fn (clos, hdr') => emitClosure clos o hdr') *)
           (*                     hdr escapeClos *)
           (*     val env' = foldl (fn (c, e) => addClosure e (closureID c, c)) *)
           (*                      env escapeClos *)
           (*     val nenv = foldl *)
           (*       (fn (f, nenv) => addProtocol nenv *)
           (*         (f, Recursion { label=CPS.LABEL (#2 f), pvd=pvd, standard=false })) *)
           (*       nenv known *)
           (*     val nenv = foldl *)
           (*       (fn (f, nenv) => addProtocol nenv *)
           (*         (f, Recursion { label=CPS.LABEL (#2 f), pvd=pvd, standard=true })) *)
           (*       nenv escape *)
           (*     val env' = foldl *)
           (*       (fn (f, env') => addProtocol env' *)
           (*         (f, KnownFunction { label=CPS.LABEL (#2 f), pvd=pvd })) *)
           (*       env' known *)
           (*     val env' = foldl *)
           (*       (fn (f, env') => addProtocol env' (f, StandardFunction)) *)
           (*       env' escape *)
           (*     val knownFrag = foldl *)
           (*       (fn ((kind, name, args, tys, body), frag) => *)
           (*         let val (args', tys', nenv) = *)
           (*               adjustFormalArgs (nenv, args, tys) *)
           (*             val args' = args' @ pvd *)
           (*         in  (nenv, (kind, name, args', tys', body))::frag *)
           (*         end) *)
           (*       [] known *)
           (*     val escapeFrag = foldl *)
           (*       (fn ((kind, name, args, tys, body), frag) => *)
           (*         let val (link, clos) = (LV.mkLvar(), LV.mkLvar()) *)
           (*             val args' = link::clos::args *)
           (*             val tys' = gpType()::gpType()::tys *)
           (*             val (args', tys', nenv) = *)
           (*               adjustFormalArgs (nenv, args, tys) *)
           (*         in  (nenv, (kind, name, args', tys', body))::frag *)
           (*         end) *)
           (*       [] escape *)
           (*     (hdr, knownFrag @ escapeFrag) *)

  (* val makeEnv = fn (env, prop, fs) => *)
  (*   let fun strFs () = *)
  (*         concat ["[", String.concatWithMap ", " (LV.lvarName o #2) fs, "]"] *)
  (*       val () = (print ("BEFORE makeEnv for " ^ strFs () ^ " env:\n"); *)
  (*                 printEnv env; print "\n") *)
  (*       val (res as (hdr, env', frags)) = makeEnv (env, prop, fs) *)
  (*         handle e => (print (strFs ()); raise e) *)
  (*       fun pf (nenv, f: LCPS.function) = *)
  (*         (print ("FRAGMENT " ^ LV.lvarName (#2 f) ^ "\n"); *)
  (*          printEnv nenv; print "\n") *)
  (*       val () = app pf frags *)
  (*       val () = (print "AFTER makeEnv:\n"; printEnv env'; print "\n") *)
  (*   in  res *)
  (*   end *)

  exception Skip

  fun closeFix prop (env, f as (kind, name, args, tys, body)) =
        (
         (* print ("converting fragment: " ^ LV.lvarName name ^ "\n"); *)
         (* printCPS f; *)
         (kind, name, args, tys, close (env, prop, body)))
         handle e => (print ("In function " ^ LV.lvarName name ^ "\n"); raise e)
  and close (env, prop, cexp) =
        (case cexp
          of LCPS.FIX (label, bindings, e) =>
               let val (hdr, nenv, frags) = makeEnv (env, prop, bindings)
                   (* val () = print "END makeEnv\n" *)
               in  LCPS.FIX (label,
                             map (closeFix prop) frags,
                             hdr (close (nenv, prop, e)))
               end
           | LCPS.APP (label, CPS.VAR f, args) =>
               (case protocolOf env f
                  of KnownFunction { label, pvd } =>
                       let val f' = CPS.LABEL label
                           val (args', hdr) = fixActualArgs (env, args)
                           val pvd = map CPS.VAR pvd
                           val hdr' = fixAccess (env, pvd)
                           val args' = args' @ pvd
                       in  hdr (hdr' (LCPS.APP (label, f', args')))
                       end
                   | Recursion { label, pvd } =>
                       let val f' = CPS.LABEL label
                           val (args', hdr) = fixActualArgs (env, args)
                           val pvd = map CPS.VAR pvd
                           val hdr' = fixAccess (env, pvd)
                           val args' = args' @ pvd
                       in  hdr (hdr' (LCPS.APP (label, f', args')))
                       end
                   | StandardFunction =>
                       let val f' = CPS.VAR f
                           val hdr1 = fixAccess (env, [f'])
                           val (args', hdr2) = fixActualArgs (env, args)
                           val hdr = hdr1 o hdr2
                           val l = LV.mkLvar ()
                       in  hdr (LCPS.SELECT (LV.mkLvar(), 0, f', l, CPS.FUNt,
                                  LCPS.APP (label, CPS.VAR l,
                                    (CPS.VAR l)::f'::args')))
                       end
                   | StandardContinuation { callee, gpcs, fpcs } =>
                       let val f' = callee
                           val args = gpcs @ fpcs @ args
                           val hdr  = fixAccess (env, f'::args)
                       in  hdr (LCPS.APP (label, f', f' :: args))
                       end)
           | LCPS.APP (_, _, _) => raise Fail "call???"
           | LCPS.RECORD (label, rk, elems, name, e) =>
               let val hdr = fixAccess (env, map #2 elems)
                   val env' = env addImms [name]
               in  hdr (LCPS.RECORD (label, rk, elems, name,
                                     close (env', prop, e)))
               end
           | LCPS.SELECT (label, n, v, x, ty, e) =>
               let val hdr = fixAccess (env, [v])
                   val env' = env addImms [x]
               in  hdr (LCPS.SELECT (label, n, v, x, ty,
                                     close (env', prop, e)))
               end
           | LCPS.OFFSET _ => raise Fail "offset"
           | LCPS.SWITCH (label, v, x, branches) =>
               let val hdr = fixAccess (env, [v])
               in  hdr (LCPS.SWITCH (label, v, x,
                          map (fn e => close (env, prop, e)) branches))
               end
           | LCPS.BRANCH (label, b, args, x, con, alt) =>
               let val hdr = fixAccess (env, args)
               in  hdr (LCPS.BRANCH (label, b, args, x,
                          close (env, prop, con),
                          close (env, prop, alt)))
               end
           | LCPS.SETTER (label, s, args, e) =>
               let val hdr = fixAccess (env, args)
               in  hdr (LCPS.SETTER (label, s, args, close (env, prop, e)))
               end
           | LCPS.LOOKER (label, l, args, x, ty, e) =>
               let val hdr = fixAccess (env, args)
                   val env' = env addImms [x]
                   val e' = close (env', prop, e)
               in  hdr (LCPS.LOOKER (label, l, args, x, ty, e'))
               end
           | LCPS.ARITH (label, a, args, x, ty, e) =>
               let val hdr = fixAccess (env, args)
                   val env' = env addImms [x]
                   val e' = close (env', prop, e)
               in  hdr (LCPS.ARITH (label, a, args, x, ty, e'))
               end
           | LCPS.PURE (label, p, args, x, ty, e) =>
               let val hdr = fixAccess (env, args)
                   val env' = env addImms [x]
                   val e' = close (env', prop, e)
               in  hdr (LCPS.PURE (label, p, args, x, ty, e'))
               end
           | LCPS.RCC (l, b, name, ty, args, res, e) =>
               let val hdr = fixAccess (env, args)
                   val env' = raise Fail "TODO"
                   val e' = close (env', prop, e)
               in  hdr (LCPS.RCC (l, b, name, ty, args, res, e'))
               end)
               handle Skip => raise Skip
                    |    e => (print (concat ["Error: ", exnMessage e, "\n"]);
                               printExp cexp; raise Skip)

  fun closeCPS ((kind, name, args, tys, body), cg, info, prop) =
    let val initEnv =
          Env { immediates=[], calleeSaves=[], closures=[],
                protocols=LV.Map.singleton (name, StandardFunction),
                allocated=LV.Tbl.mkTable (32, ClosureEnv), cg=cg, info=info }
        val (link, clos) = (LV.mkLvar (), LV.mkLvar ())
        val args' = link::clos::args
        val tys'  = CPSUtil.BOGt::CPSUtil.BOGt::tys
        val (args', tys', env') = adjustFormalArgs (initEnv, args', tys')
    in  closeFix prop (env', (kind, name, args', tys', body))
    end

  fun convert (cps, cg, info)  =
    let
      val cps = assignFunKind (cps, cg, info)
      (* val () = (print ">>>after fk\n"; PPCps.printcps0 (LCPS.unlabelF cps); *)
      (*           print "<<<after fk\n") *)
      val sn = installStageNumbers (cps, cg, info)
      val freeInEscape = calculateFreeInEscape (cg, info) : LCPS.function -> bool
      val () = dumpStageNumbers sn
      val cps = closeCPS (cps, cg, info, (sn, freeInEscape))
      val () = print ">>>>>>>>>>>>>>>>>> AFTER <<<<<<<<<<<<<<<<<<<<\n"
      val () = printCPS cps
      val () = print ">>>>>>>>>>>>>>>>>>  END  <<<<<<<<<<<<<<<<<<<<\n"
    in
      cps
    end
end
