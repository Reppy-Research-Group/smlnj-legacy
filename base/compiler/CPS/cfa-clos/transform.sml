structure Transform :> sig
  val transform
    : LabelledCPS.function * ClosureDecision.t * Web.t * SyntacticInfo.t
   -> LabelledCPS.function
end = struct
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo
  structure W = Web
  structure G = Group

  val bogusTy = CPS.PTRt CPS.VPT
  val defunTy = CPS.NUMt { sz=Target.defaultIntSz, tag=true }

  datatype path = Path of { base: LV.lvar, selects: int list }
                | Create of { function: LCPS.function,
                              env: { base: LV.lvar, selects: int list } option }

  fun pathToS (Path {base, selects}) =
        concat (LV.lvarName base :: map (fn i => "." ^ Int.toString i) selects)
    | pathToS (Create {function, env}) =
        concat (["{", LV.lvarName (#2 function), ","] @
                (case env
                   of NONE => []
                    | SOME { base, selects } =>
                        LV.lvarName base ::
                        map (fn i => "." ^ Int.toString i) selects))

  fun mergePath (Path { base=b1, selects=s1 }, Path { base=b2, selects=s2 }) =
        if List.length s1 <= List.length s2 then
          Path { base=b1, selects=s1 }
        else
          Path { base=b2, selects=s2 }
    | mergePath ((Create _, p as Path _) | (p as Path _, Create _)) = p
    | mergePath (Create _, Create _) =
        raise Fail "There can't be two ways to get to a mut rec func"

  datatype value = Function of {
                     code: D.code,
                     env: D.environment,
                     knowncode: LCPS.function option,
                     pkg: CPS.lvar option
                   }
                 | Value of CPS.cty

  fun tagInt i =
    CPS.NUM { ival=IntInf.fromInt i, ty={ sz=Target.defaultIntSz, tag=true }}

  fun freshLV lvar = LV.dupLvar lvar
  fun freshNLV (lvar, n) = lvar :: List.tabulate (n - 1, fn _ => freshLV lvar)

  fun sameF (f: LCPS.function) (g: LCPS.function) = LV.same (#2 f, #2 g)

  fun valueToS (Function { code, env, knowncode, pkg }) =
        concat [D.codeToS code, "(", D.envToS env, "...) pkg: ",
                (case pkg of NONE => "(none)" | SOME v => LV.lvarName v),
                " known code: ",
                (case knowncode of NONE => "(none)" | SOME f => LV.lvarName (#2
                f))]
    | valueToS (Value ty) = concat ["[V (", CPSUtil.ctyToString ty, ")]"]

  structure Context :> sig
    type t

    val initial    : unit -> t
    val newContext : t * path LV.Map.map -> t

    val addfun : t * LCPS.lvar * D.code * D.environment * LCPS.function option -> t
    val addval : t * LCPS.lvar * CPS.cty -> t
    val addInScope : t * LCPS.lvar -> t

    val protocolOf  : t * LCPS.lvar -> value
    val expansionOf : t * LCPS.lvar * int -> D.slot
    val isInScope : t * LCPS.lvar -> bool
    val pathOf : t * LCPS.lvar -> path option

    val dump : t -> unit
  end = struct

    datatype t = T of {
      access: path LV.Map.map,
      protocol: value LV.Map.map,
      inscope: LV.Set.set
    }

    fun initial () =
      T { access=LV.Map.empty, protocol=LV.Map.empty, inscope=LV.Set.empty }

    fun newContext (T {protocol, ...}, access) =
      T { access=access, protocol=protocol, inscope=LV.Set.empty }

    fun addfun (T {access, protocol, inscope}, v, code, env, known) =
      T { access=access,
          protocol=LV.Map.insert
            (protocol, v, Function { code=code, env=env, knowncode=known, pkg=NONE }),
          inscope=inscope }

    fun addval (T {access, protocol, inscope}, v, ty) =
      T { access=access,
          protocol=LV.Map.insert (protocol, v, Value ty),
          inscope=inscope }

    fun addInScope (T {access, protocol, inscope}, v) =
      T { access=access, protocol=protocol, inscope=LV.Set.add (inscope, v) }

    fun protocolOf (T {protocol, ...}, v) = LV.Map.lookup (protocol, v)
         handle NotFound => raise Fail ("Not in scope: " ^ LV.lvarName v)


    fun isInScope (T {inscope, ...}, v) =
      LV.Set.member (inscope, v)

    fun pathOf (T {access, ...}, v) = LV.Map.find (access, v)

    fun dump (T {access, protocol, inscope}) =
      let
        val p = app print
        val cwm = String.concatWithMap
        fun paccess (v, path) =
          p ["  ", LV.lvarName v, " --> ", pathToS path, "\n"]
        fun pprotocol (v, proto) =
          p ["  ", LV.lvarName v, " --> [", valueToS proto, "]\n"]
      in
        p ["== Access ==\n"];
        LV.Map.appi paccess access;
        p ["== Protocol ==\n"];
        LV.Map.appi pprotocol protocol;
        p ["== InScope ==\n"];
        p ["[", cwm "," LV.lvarName (LV.Set.listItems inscope), "]"]
      end

    fun expansionOf (t, v, i) =
      (case protocolOf (t, v)
         of Function { code=_, env=D.Flat slots, knowncode=_, pkg=_ } =>
              (List.sub (slots, i)
               handle Subscript =>
               raise Fail (concat
                 ["Invalid expansion #", Int.toString i, " of ", LV.lvarName v,
                  ": [", String.concatWithMap "," D.slotToString slots, "]"]))
          | _ => raise Fail (concat ["Invalid expansion: ", LV.lvarName v,
            " is not a function"]))
      handle e => (dump t; raise e)
  end

  structure C = Context

  type env = C.t * D.t * W.t * S.t

  val varOfEnv = EnvID.unwrap : EnvID.t -> LCPS.lvar

  fun funkindToTy (CPS.CONT | CPS.KNOWN_CONT) = CPS.CNTt
    | funkindToTy _ = CPS.FUNt

  fun slotToVar (D.Var (v, _)) = v
    | slotToVar _ = raise Fail "expect Var of Slot"

  fun slotToVal ctx (D.EnvID e) = CPS.VAR (varOfEnv e)
    | slotToVal ctx (D.Var (v, _)) = CPS.VAR v
    | slotToVal ctx (D.Code f) = CPS.LABEL (#2 f)
    | slotToVal ctx (D.Expand (v, i, ty)) =
        slotToVal ctx (C.expansionOf (ctx, v, i) handle e => raise e)
    | slotToVal ctx (D.ExpandAny _) = raise Fail "unresolved any"
    | slotToVal ctx D.Null = tagInt 0

  (* envcp:
   * 1. polluted user: code is (#1).1
   * 2. polluted cont: code is #1
   * 3. singleton web: code is direct
   * 4. otherwise web: code is .1 if boxed, and #1 if unboxed
   *    FIXME: There really should be a way to communicate where the code is
   *    from the decision.
   *)

  fun slotToArg ctx (D.EnvID v) = (varOfEnv v, bogusTy)
    | slotToArg ctx (D.Var (v, ty)) = (v, ty)
    | slotToArg ctx (D.Expand (v, i, ty)) =
        slotToArg ctx (C.expansionOf (ctx, v, i) handle e => raise e)
    | slotToArg ctx (D.Code f) = (#2 f, funkindToTy (#1 f))
    | slotToArg ctx (D.ExpandAny _) = raise Fail "unresolved any"
    | slotToArg ctx D.Null = (LV.mkLvar (), bogusTy)

  fun envargs (ctx: C.t, code: D.code, env: D.environment, kind)
    : (CPS.lvar * CPS.cty) list =
    let val slots =
          (case env
             of D.Flat slots => map (slotToArg ctx) slots
              | D.Boxed e => [(varOfEnv e, bogusTy)])
        val funty = (case kind of Web.Cont => CPS.CNTt | Web.User => CPS.FUNt)
        val codep =
          (case code
             of D.Pointer v => [(v, funty)]
              | D.SelectFrom _ => []
              | D.Defun (v, _) => [(v, defunTy)]
              | D.Direct _ => [])
    in  codep @ slots
    end

  fun slotToTy (D.EnvID _)  = CPS.PTRt CPS.VPT
    | slotToTy (D.Var   (v, ty)) = ty
    | slotToTy (D.Expand (v, i, ty)) = ty
    | slotToTy (D.ExpandAny _) = raise Fail "unresolved any"
    | slotToTy (D.Code   f) =
        (case #1 f
           of (CPS.CONT | CPS.KNOWN_CONT) => CPS.CNTt
            | _ => CPS.FUNt)
    | slotToTy D.Null       =  CPS.NUMt { sz=Target.defaultIntSz, tag=true }

  fun envszUnchecked ((ctx, _, web, syn): env, repr, v) =
    (case Web.webOfVar (web, v)
       of SOME w =>
           (case Web.content (web, w)
              of { polluted=true, kind=Web.Cont, ... } =>
                   SOME [bogusTy, bogusTy, bogusTy] (* FIXME: Magic number *)
               | { polluted=true, kind=Web.User, ... } =>
                   SOME [bogusTy]
               | { polluted=false, defs, kind, ... } =>
                   let val f = Vector.sub (defs, 0)
                       val D.Closure {code, env} = LCPS.FunMap.lookup (repr, f)
                       val funty = (case kind
                                      of Web.Cont => CPS.CNTt
                                       | Web.User => CPS.FUNt)
                       val tys = (case env
                                    of D.Boxed _ => [bogusTy]
                                     | D.Flat slots => map slotToTy slots)
                   in  SOME tys
                   end)
        | NONE =>
           (case S.typeof syn v
              of CPS.CNTt => SOME [CPS.CNTt, bogusTy, bogusTy, bogusTy]
               | ty => NONE))

  fun singlevec #[f] = SOME f
    | singlevec _ = NONE

  fun checkWeb (repr, defs) : unit =
    let val (f, fs) =
          (case Vector.toList defs
             of [] => raise Fail "empty web"
              | (f :: fs) => (f, fs))
        fun getCodeEnv f =
          let val D.Closure {code, env} = LCPS.FunMap.lookup (repr, f)
          in  (code, env)
          end
        fun checkCode (D.Direct _, D.Direct _) = ()
          | checkCode (D.Pointer _, D.Pointer _) = ()
          | checkCode (D.SelectFrom _, D.SelectFrom _) = ()
          | checkCode (D.Defun _, D.Defun _) = ()
          | checkCode _ = raise Fail "Inconsistent code pointer"
        fun checkEnv (D.Boxed _, D.Boxed _) = ()
          | checkEnv (D.Flat slots, D.Flat slots2) =
              if List.length slots = List.length slots2 then
                ()
              else
                raise Fail "arity"
          | checkEnv _ = raise Fail "Flat Boxed"
        val (refcode, refenv) = getCodeEnv f
        val () =
          (case (refcode, refenv)
             of (D.Pointer _, D.Boxed _) => raise Fail "pointer - boxed"
              | (D.SelectFrom _, D.Flat _) => raise Fail "select - flat"
              | _ => ())
    in  List.app (fn g =>
          let val (code, env) = getCodeEnv g
          in  checkCode (code, refcode); checkEnv (env, refenv)
          end
        ) fs
    end

  fun webenv ((ctx, D.T {repr, ...}, web, syn): env, v) :
    Web.kind * D.code * D.environment * LCPS.function option =
    (case Web.webOfVar (web, v)
       of SOME w =>
           (case Web.content (web, w)
              of { polluted=true, kind=Web.Cont, ... } =>
                   (* Default cont *)
                   (Web.Cont,
                    D.Pointer v,
                    D.Flat [D.Var (freshLV v, bogusTy),
                            D.Var (freshLV v, bogusTy),
                            D.Var (freshLV v, bogusTy)],
                    NONE)
               | { polluted=true, kind=Web.User, ... } =>
                   (Web.User,
                    D.SelectFrom { env=0, selects=[0] },
                    D.Flat [D.Var (v, bogusTy)],
                    NONE)
               | { polluted=false, defs, kind, ... } =>
                   let val f = Vector.sub (defs, 0)
                       val D.Closure {code, env} = LCPS.FunMap.lookup (repr, f)
                       val code =
                         (case code
                            of D.Direct f => D.Direct f
                             | D.Pointer _ => D.Pointer v
                             | D.SelectFrom sel => D.SelectFrom sel
                             | D.Defun (_, defs) => D.Defun (v, defs))
                       val env =
                         (case env
                            of D.Boxed e =>
                                 D.Boxed (EnvID.wrap v)
                             | D.Flat slots =>
                                 D.Flat
                                   (map (fn s => D.Var (freshLV v, slotToTy s))
                                        slots))
                       val () = checkWeb (repr, defs)
                   in  (kind, code, env, singlevec defs)
                   end)
        | NONE =>
           (case S.typeof syn v
              of CPS.CNTt =>
                   (Web.Cont,
                    D.Pointer v,
                    D.Flat [D.Var (freshLV v, bogusTy),
                            D.Var (freshLV v, bogusTy),
                            D.Var (freshLV v, bogusTy)],
                    NONE)
               | _ =>
                   (Web.User,
                    D.SelectFrom { env=0, selects=[0] },
                    D.Boxed (EnvID.wrap v),
                    NONE)))

  fun funkind (env as (_, dec, _, syn): env, function: LCPS.function) =
    let val (kind, name, _, _, _) = function
        val D.T { repr, ... } = dec
        val D.Closure { code, ... } = LCPS.FunMap.lookup (repr, function)
        fun directCall (D.Direct _) = true
          | directCall _ = false
    in  if directCall code (* orelse LCPS.Set.all isCall uses *) then
          CPS.KNOWN
        else
          (case kind
             of CPS.KNOWN_CONT => CPS.KNOWN
              | CPS.CONT => CPS.CONT
              | _ => CPS.ESCAPE)
    end

  val _ = slotToVar : D.slot -> CPS.lvar
  val _ = slotToVal : C.t -> D.slot -> CPS.value

  fun buildAccessMap (env: env, f: LCPS.function, muts) : path LV.Map.map =
    let val (ctx, D.T { repr, heap, ... }, _, _) = env
        (* val roots  = LCPS.FunMap.lookup (repr, f) *)
        val insert = LV.Map.insertWith mergePath
        fun nexts (e, { base, selects }, todo) =
          (case EnvID.Map.find (heap, e)
             of SOME (D.Record (slots, _)) =>
                  List.foldli (fn (i, s, todo) =>
                    ((s, { base=base, selects=selects@[i] }) :: todo))
                    todo slots
              | SOME (D.RawBlock (vars, _)) =>
                  List.foldli (fn (i, v, todo) =>
                    ((D.Var (v, bogusTy),
                      { base=base, selects=selects@[i] })::todo))
                    todo vars
              | NONE => raise Fail "nexts")
        fun slotToKey (D.Var (v, _)) = v
          | slotToKey (D.Expand (v, i, _)) =
              slotToKey (C.expansionOf (ctx, v, i) handle e => raise e)
          | slotToKey (D.ExpandAny _) = raise Fail "unresolved any"
          | slotToKey (D.EnvID e) = varOfEnv e
          | slotToKey D.Null = raise Fail "unexpected null"
          | slotToKey (D.Code _) = raise Fail "unexpected code"

        fun dfs ([], access) = access
          | dfs ((s, path) :: todo, access) =
              (case s
                 of D.Var (v, ty) => dfs (todo, insert (access, v, Path path))
                  | D.Expand (v, i, ty) =>
                      dfs ((C.expansionOf (ctx, v, i) handle e => raise e, path) :: todo,
                           access)
                  | D.ExpandAny _ => raise Fail "unresolved any"
                  | D.EnvID e =>
                      dfs (nexts (e, path, todo),
                           insert (access, varOfEnv e, Path path))
                  | D.Null => dfs (todo, access)
                  | D.Code _ => dfs (todo, access))
        val slots =
          (case C.protocolOf (ctx, #2 f)
             of Function {code, env, pkg, knowncode} =>
                  (case env
                     of D.Boxed e => [D.EnvID e]
                      | D.Flat slots => slots)
              | Value _ => raise Fail "impossible")
          handle e => raise e
        val names = #1 (ListPair.unzipMap (slotToArg ctx) slots)
        val bases =
          ListPair.foldl (fn (name, slot, bases) =>
            (slot, { base=name, selects=[] }) :: bases) [] (names, slots)
        val access = dfs (bases, LV.Map.empty)

        val access =
          foldl (fn (g, access) =>
            if sameF f g then
              access
            else
              let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, g)
              in  case (code, env)
                    of (D.SelectFrom _, D.Boxed e) =>
                          (* If the mutually recursive functions need a pointer,
                           * we create one from the base. *)
                          let val sharedEnv =
                                (case EnvID.Map.lookup (heap, e)
                                   of D.Record ([D.Code _, slot], _) =>
                                        SOME slot
                                    | D.Record ([D.Code _], _) => NONE
                                    | _ => raise Fail "unexpected repr")
                              (* REFACTOR: I don't really like the fact that we
                               * are getting the name of the shared env via its
                               * position. Maybe repr should be a map from
                               * Group instead of functions, and a closure has a
                               * list of functions. *)
                              val path =
                                Option.map (fn slot =>
                                  (case LV.Map.lookup (access, slotToKey slot)
                                     of Path path => path
                                      | Create _ => raise Fail "impossible")
                                ) sharedEnv
                          in  insert (access, varOfEnv e,
                                Create { function=g, env=path })
                          end
                    | (D.Direct _, D.Boxed e) => access
                    | (_, D.Boxed _) => raise Fail "check this"
                    | _ => access
              end
            ) access muts
    in  access
    end

  fun indexOf (pred: 'a -> bool) (xs: 'a list) : int =
    (case List.findi (fn (_, y) => pred y) xs
       of SOME (i, _) => i
        | NONE => raise Subscript)

  type header = LCPS.cexp -> LCPS.cexp

  (* TODO: generate correct type for intermediate record selection *)
  (* TODO: CSE *)
  fun pathToHdr (SOME (Path { base, selects }), name, cty) : header =
        let fun select [] v =
                  if LV.same (base, name) then
                    fn e => e
                  else
                    raise Fail "Doing so require renaming"
              | select [i] v =
                  (fn cexp =>
                    LCPS.SELECT (LCPS.mkLabel (), i, CPS.VAR v, name, cty, cexp))
              | select (i::selects) v =
                  let val name' = LV.dupLvar name
                  in  fn cexp =>
                        LCPS.SELECT (LCPS.mkLabel (), i, CPS.VAR v, name', bogusTy,
                                     select selects name' cexp)
                  end
        in  select selects base
        end
    | pathToHdr (SOME (Create { function, env }), name, cty) =
        let fun accesspath [] = CPS.OFFp 0
              | accesspath (i :: is) = CPS.SELp (i, accesspath is)
            val fields =
              (case env
                 of SOME {base, selects} =>
                      [(LCPS.mkLabel (), CPS.VAR base, accesspath selects)]
                  | NONE => [])
            val fields =
              (LCPS.mkLabel (), CPS.LABEL (#2 function), CPS.OFFp 0) :: fields
        in  fn cexp =>
              LCPS.RECORD (LCPS.mkLabel (), CPS.RK_ESCAPE, fields, name, cexp)
        end
    | pathToHdr (NONE, name, cty) : header = fn x => x

  fun fixaccess1 (env: env, CPS.VAR v) : header * env =
        let val (ctx, dec, web, syn) = env
        in  if C.isInScope (ctx, v) then
              (fn cexp => cexp, env)
            else
              let val path = C.pathOf (ctx, v)
                  val hdr  = pathToHdr (path, v, S.typeof syn v)
              in  (hdr, (C.addInScope (ctx, v), dec, web, syn))
              end
        end
    | fixaccess1 (env: env, _: CPS.value) = (fn cexp => cexp, env)

  fun fixaccess (env: env, values: CPS.value list) : header * env =
    List.foldl (fn (v, (hdr, env)) =>
      let val (hdr', env) = fixaccess1 (env, v)
      in  (hdr o hdr', env)
      end) (fn cexp => cexp, env) values

  fun allocate1 (env as (ctx, dec, _, syn): env, e: EnvID.t) : header * env =
    let val D.T { heap, ... } = dec
        val object = EnvID.Map.lookup (heap, e)
        (* FIXME: if there is mutbox to allocate, need to allocate here *)
        val (fields, recKind) =
          (case object
             of D.Record (slots, _) => (map (slotToVal ctx) slots, CPS.RK_ESCAPE)
              | D.RawBlock (vs, rk) => (map CPS.VAR vs, rk))
        val (hdr, env as (ctx, dec, web, syn)) = fixaccess (env, fields)
        val name = varOfEnv e
        val fields = map (fn f => (LCPS.mkLabel (), f, CPS.OFFp 0)) fields
        val () = if List.null fields then
                   (D.dump (dec, syn); raise Fail "GC is not gonna like this")
                 else ()
        val hdr = fn cexp =>
          hdr (LCPS.RECORD (LCPS.mkLabel (), recKind, fields, name, cexp))
    in  (hdr, (C.addInScope (ctx, name), dec, web, syn))
    end

  fun allocate (env: env, es: EnvID.t list) : header * env =
    List.foldl (fn (e, (hdr, env)) =>
      let val (hdr', env) = allocate1 (env, e)
      in  (hdr o hdr', env)
      end) (fn cexp => cexp, env) es

  fun expandargs (env: env, args: LCPS.lvar list, tys: LCPS.cty list)
    : LCPS.lvar list * CPS.cty list * env =
    let val (ctx, dec as D.T {repr, ...}, web, syn) = env
        fun dupN (n, []) = ([], [])
          | dupN (n, ty :: tys) =
              let val (names, tys) =
                    ListPair.unzipMap (fn ty => (freshLV n, ty)) tys
              in  (n :: names, ty :: tys)
              end
        fun expand (x, ty, (args, ts, ctx)) =
          (case ty
             of (CPS.FUNt | CPS.CNTt) =>
                  let val (kind, code, environ, known) = webenv (env, x)
                      val ctx = C.addfun (ctx, x, code, environ, known)
                      val newargs = envargs (ctx, code, environ, kind)
                      val (xs, tys) = ListPair.unzip newargs
                  in  (xs @ args, tys @ ts, ctx)
                  end
              | _ => (* this is not a function *)
                  (x :: args, ty :: ts, C.addval (ctx, x, ty)))
        val (args, tys, ctx) = ListPair.foldr expand ([], [], ctx) (args, tys)
    in  (args, tys, (ctx, dec, web, syn))
    end

  fun expandval (env: env, values: CPS.value list) : CPS.value list =
    let val (ctx, _, _, _) = env
        fun cvt (CPS.VAR v) =
          (case C.protocolOf (ctx, v) handle e => raise e
             of Function { code, env, knowncode, ... } =>
                  let val slots =
                        (case env
                           of D.Boxed e => [CPS.VAR (varOfEnv e)]
                            | D.Flat slots => map (slotToVal ctx) slots)
                      val cd =
                        (case (code, knowncode)
                           of (D.Pointer _, SOME f) => [CPS.LABEL (#2 f)]
                            | (D.Pointer v, NONE) => [CPS.VAR v]
                            | (D.Defun (_, fs), SOME f) =>
                                [tagInt (indexOf (sameF f) fs)]
                            | (D.Defun (f, fs), NONE) => [CPS.VAR f]
                            | _ => [])
                  in  cd @ slots
                  end
              | Value ty => [CPS.VAR v])
          | cvt value = [value]
        fun collect (v, vs) = (cvt v @ vs)
    in  foldr collect [] values
    end

  fun fixaccess' (env: env, values: CPS.value list)
    : CPS.value list * header * env =
    let val args = expandval (env, values)
        val () = if List.length args <> List.length values then
                   raise Fail "Expansion different length"
                 else
                   ()
        val (hdr, env) = fixaccess (env, args)
    in  (args, hdr, env)
    end

  fun fixaccess1' (env: env, value: CPS.value) =
    let val (values, hdr, env) = fixaccess' (env, [value])
    in  (List.hd values, hdr, env)
    end

  fun addvar (e as (ctx, dec, web, syn): env, name: CPS.lvar, CPS.FUNt): env =
        (* CNT is not going to be here *)
        let val (kind, code, environ, known) = webenv (e, name)
            val ctx = C.addfun (ctx, name, code, environ, known)

            (* CHECKING *)
            val newargs = envargs (ctx, code, environ, kind)
            val () = if List.length newargs <> 1 then
                       (app print ["selecting to ", LV.lvarName name,
                                   " expects calling convention: ",
                                   D.closureToS
                                     (D.Closure {code=code, env=environ}),
                                   "\n"];
                        raise Fail "bad protocol")
                      else
                        ()
            (* END CHECKING *)
        in  (ctx, dec, web, syn)
        end
   | addvar ((ctx, dec, web, syn), name, ty) =
        (C.addval (ctx, name, ty), dec, web, syn)

  fun needLinkReg (web, w) =
    let val { defs, uses, polluted, kind } = W.content (web, w)
    in  if not polluted andalso Vector.length defs = 1 then
          false
        else
          true
    end

  fun closefun (env: env, functions) (f as (fk, name, args, tys, body)) =
    let val (ctx, dec as D.T {repr, ...}, web, syn) = env
        val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
        val (envs, envtys) =
          (case env
             of D.Boxed e => ([varOfEnv e], [bogusTy])
              | D.Flat slots => ListPair.unzipMap (slotToArg ctx) slots)
        val insideenv =
          (case env
             of D.Boxed e => D.Boxed e
              | D.Flat slots =>
                  let
                      (* val slots = *)
                      (*   ListPair.mapEq (fn (D.Null, v) => D.Var (v, bogusTy) *)
                      (*                    | (s, _) => s) (slots, envs) *)
                  in  D.Flat slots
                  end)
        val env =
          let val ctx =  C.addfun (ctx, #2 f, code, insideenv, SOME f)
              val accessMap = buildAccessMap ((ctx, dec, web, syn), f, functions)
              val ctx = C.newContext (ctx, accessMap)
              val ctx = foldl (fn (v, ctx) => C.addInScope (ctx, v)) ctx envs
          in  (ctx, dec, web, syn)
          end
        val (args, tys, env) = expandargs (env, args, tys)
        (* LINK *)
        val fk = funkind (env, f)
        val (args, tys) =
          (case funkind (env, f)
             of CPS.KNOWN => (envs @ args, envtys @ tys)
              | _ => (freshLV name :: envs @ args, bogusTy :: envtys @ tys))
        (* val () = app print ["IN FUNCTION ", LV.lvarName name, "\n"] *)
        (* val () = C.dump (#1 env) *)
        (* val () = print "\n" *)
    in  (fk, name, args, tys, close (env, body))
    end
  and close (env, cexp as LCPS.FIX (label, bindings, exp)) =
        let val group = G.fromExp cexp
            val D.T { allo, repr, ... } = #2 env
            val envs  = Option.getOpt (G.Map.find (allo, group), [])
            val (allocateHdr, env) = allocate (env, envs)
            fun addproto (f, (ctx, dec, syn, web)) =
              let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
              in  (C.addfun (ctx, #2 f, code, env, SOME f), dec, syn, web)
              end
            val env = foldl addproto env bindings
            val bindings = map (closefun (env, bindings)) bindings
            (* val () = app print ["AFTER FIX ", String.concatWithMap "," *)
            (* (LV.lvarName o #2) bindings, "\n"] *)
            (* val () = C.dump (#1 env) *)
            (* val () = print "\n" *)
        in  LCPS.FIX (label, bindings, allocateHdr (close (env, exp)))
        end
    | close (env as (ctx, dec, web, syn), LCPS.APP (label, CPS.VAR f, args)) =
        let val args = expandval (env, args)
            val (hdr, env) = fixaccess (env, args)
            val mklab = LCPS.mkLabel
            val label = CPS.LABEL o (#2: LCPS.function -> LCPS.lvar)
            val var = CPS.VAR
            val (code, environ, knowncode, pkg) =
              (case C.protocolOf (ctx, f)
                 of Value _ =>
                      let val (_, code, environ, knowncode) = webenv (env, f)
                      in  (code, environ, knowncode, NONE)
                      end
                  | Function { code, env, knowncode, pkg } =>
                      (code, env, knowncode, pkg))
              handle e => raise e
            val envargs =
              (case environ
                 of D.Boxed e => [var (varOfEnv e)]
                  | D.Flat slots => map (slotToVal ctx) slots)
            val (hdr', env) = fixaccess (env, envargs)
            val args = envargs @ args
            val hdr = hdr o hdr'
        in  case (code, knowncode)
              of (D.Direct f, _) =>
                   hdr (LCPS.APP (mklab (), label f, args))
               | (D.Pointer f, NONE) =>
                   let val (hdr', env) = fixaccess1 (env, var f)
                       val call = LCPS.APP (mklab (), var f, var f :: args)
                   in  hdr (hdr' call)
                   end
               | (D.Pointer _, SOME f) =>
                   let val call = LCPS.APP (mklab (), label f, label f :: args)
                   in  hdr call
                   end
               | (D.SelectFrom { env, selects }, NONE) =>
                   let val name = freshLV f
                       val ty = S.typeof syn f
                       val clos =
                         (case List.sub (envargs, env)
                            of CPS.VAR v => v
                             | _ => raise Fail "selecting from a nonptr")
                       val hdr' = pathToHdr
                                    (SOME (Path {base=clos, selects=selects}),
                                     name, ty)
                       val call = LCPS.APP (mklab (), var name, var name::args)
                   in  hdr (hdr' call)
                   end
               | (D.SelectFrom _, SOME f) =>
                   let val call = LCPS.APP (mklab (), label f, label f :: args)
                   in  hdr call
                   end
               | (D.Defun _, _) => raise Fail "unimp"
        end
    | close (env as (ctx, dec, web, syn), LCPS.APP (label, _, args)) =
        raise Fail "calling non-var functions"
    | close (env, LCPS.RECORD (label, rk, fields, x, exp)) =
        let val (values, hdr, env) = fixaccess' (env, map #2 fields)
            val fields = ListPair.mapEq (fn (v, (l, _, p)) => (l, v, p))
                                        (values, fields)
            val env = addvar (env, x, CPS.PTRt (CPS.RPT (List.length fields)))
        in  hdr (LCPS.RECORD (label, rk, fields, x, close (env, exp)))
        end
    | close (env, LCPS.SELECT (label, i, v, x, ty, exp)) =
        let val (v, hdr, env) = fixaccess1' (env, v)
            val env = addvar (env, x, ty)
        in  hdr (LCPS.SELECT (label, i, v, x, ty, close (env, exp)))
        end
    | close (env, LCPS.OFFSET _) = raise Fail "Offset"
    | close (env, LCPS.SWITCH (label, v, x, exps)) =
        let val (v, hdr, env) = fixaccess1' (env, v)
        in  hdr (LCPS.SWITCH (label, v, x, map (fn e => close (env, e)) exps))
        end
    | close (env, LCPS.BRANCH (label, br, args, x, exp1, exp2)) =
        let val (args, hdr, env) = fixaccess' (env, args)
        in  hdr (LCPS.BRANCH (label, br, args, x,
                   close (env, exp1), close (env, exp2)))
        end
    | close (env, LCPS.SETTER (label, st, args, exp)) =
        let val (args, hdr, env) = fixaccess' (env, args)
        in  hdr (LCPS.SETTER (label, st, args, close (env, exp)))
        end
    | close (env, LCPS.LOOKER (label, lk, args, x, ty, exp)) =
        let val (args, hdr, env) = fixaccess' (env, args)
            val env = addvar (env, x, ty)
        in  hdr (LCPS.LOOKER (label, lk, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.ARITH (label, ar, args, x, ty, exp)) =
        let val (args, hdr, env) = fixaccess' (env, args)
            val env = addvar (env, x, ty)
        in  hdr (LCPS.ARITH (label, ar, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.PURE (label, pr, args, x, ty, exp)) =
        let val (args, hdr, env) = fixaccess' (env, args)
            val env = addvar (env, x, ty)
        in  hdr (LCPS.PURE (label, pr, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.RCC (label, b, name, ty, args, rets, exp)) =
        let val (args, hdr, env) = fixaccess' (env, args)
        in  hdr (LCPS.RCC (label, b, name, ty, args, rets, close (env, exp)))
        end

  fun transform ((fk, name, args, tys, body): LCPS.function, dec, web, syn) =
    let val () =
          let val D.T { repr, ... } = dec
          in  Web.fold (fn (id, { defs, polluted, ... }, ()) =>
                if not polluted then checkWeb (repr, defs) else ()) () web
          end
        val ctx = C.initial ()
        val (ctx, args, tys) =
          (case (args, tys)
             of (ret::args, CPS.CNTt::tys) =>
                  let val link = freshLV name
                      val clos = freshLV name
                      val cs = [freshLV ret, freshLV ret, freshLV ret]
                      val cstys = [bogusTy, bogusTy, bogusTy]
                      val ctx = C.addfun
                        (ctx, ret, D.Pointer ret,
                         D.Flat (ListPair.mapEq D.Var (cs, cstys)), NONE)
                      val ctx = ListPair.foldlEq
                        (fn (v, ty, ctx) => C.addval (ctx, v, ty))
                        ctx (args, tys)
                  in  (ctx, link::clos::ret::cs@args,
                            bogusTy::bogusTy::CPS.CNTt::cstys@tys)
                  end
              | _ => raise Fail "no return in top level")
         val env = (ctx, dec, web, syn)
    in  (fk, name, args, tys, close (env, body))
    end
end
