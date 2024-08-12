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

  datatype path = Path of { base: LV.lvar, selects: int list }

  fun pathToS (Path {base, selects}) =
        concat (LV.lvarName base :: map (fn i => "." ^ Int.toString i) selects)

  fun mergePath (Path { base=b1, selects=s1 }, Path { base=b2, selects=s2 }) =
    if List.length s1 <= List.length s2 then
      Path { base=b1, selects=s1 }
    else
      Path { base=b2, selects=s2 }

  fun tagInt i =
    CPS.NUM { ival=IntInf.fromInt i, ty={ sz=Target.defaultIntSz, tag=true }}


  fun freshLV lvar = LV.dupLvar lvar
  fun freshNLV (lvar, n) = List.tabulate (n, fn _ => freshLV lvar)

  structure Context :> sig
    type t

    val initial    : unit -> t
    val newContext : t * path LV.Map.map -> t

    val addProtocol : t * LCPS.lvar * D.slot list -> t
    val addInScope : t * LCPS.lvar -> t

    val protocolOf : t * LCPS.lvar -> D.slot list
    val expansionOf : t * LCPS.lvar * int -> D.slot
    val isInScope : t * LCPS.lvar -> bool
    val pathOf : t * LCPS.lvar -> path option

    val dump : t -> unit
  end = struct
    datatype t = T of {
      access: path LV.Map.map,
      protocol: D.slot list LV.Map.map,
      inscope: LV.Set.set
    }

    fun initial () =
      T { access=LV.Map.empty, protocol=LV.Map.empty, inscope=LV.Set.empty }

    fun newContext (T {protocol, ...}, access) =
      T { access=access, protocol=protocol, inscope=LV.Set.empty }

    fun addProtocol (T {access, protocol, inscope}, v, slots) =
      T { access=access, protocol=LV.Map.insert (protocol, v, slots),
          inscope=inscope }

    fun addInScope (T {access, protocol, inscope}, v) =
      T { access=access, protocol=protocol, inscope=LV.Set.add (inscope, v) }

    fun protocolOf (T {protocol, ...}, v) =
      case LV.Map.find (protocol, v)
        of SOME slots => slots
         | NONE => [D.Var v]
         (* raise Fail ("No protocol for " ^ LV.lvarName v) *)

    fun expansionOf (t, v, i) =
      let val proto = protocolOf (t, v)
      in  List.sub (proto, i)
          handle Subscript =>
          raise Fail (concat ["Invalid expansion #", Int.toString i, " of ",
                              LV.lvarName v, ": [",
                              String.concatWithMap "," D.slotToString proto, "]"])
      end

    fun isInScope (T {inscope, ...}, v) =
      LV.Set.member (inscope, v)

    fun pathOf (T {access, ...}, v) = LV.Map.find (access, v)

    fun dump (T {access, protocol, inscope}) =
      let
        val p = app print
        val cwm = String.concatWithMap
        fun paccess (v, path) =
          p ["  ", LV.lvarName v, " --> ", pathToS path, "\n"]
        fun pprotocol (v, ss) =
          p ["  ", LV.lvarName v, " --> [", cwm "," D.slotToString ss, "]\n"]
      in
        p ["== Access ==\n"];
        LV.Map.appi paccess access;
        p ["== Protocol ==\n"];
        LV.Map.appi pprotocol protocol;
        p ["== InScope ==\n"];
        p ["[", cwm "," LV.lvarName (LV.Set.listItems inscope), "]"]
      end
  end

  structure C = Context

  type env = C.t * D.t * W.t * S.t

  val varOfEnv = EnvID.unwrap : EnvID.t -> LCPS.lvar

  fun slotToVar (D.Var v) = v
    | slotToVar _ = raise Fail "expect Var of Slot"

  fun slotToVal ctx (D.EnvID e) = CPS.VAR (varOfEnv e)
    | slotToVal ctx (D.Var v) = CPS.VAR v
    | slotToVal ctx (D.Code v) = CPS.LABEL v
    | slotToVal ctx (D.Expand (v, i)) =
        slotToVal ctx (C.expansionOf (ctx, v, i))
    | slotToVal ctx D.Null = tagInt 0

  fun slotToTy syn (D.EnvID _)  = CPS.PTRt CPS.VPT
    | slotToTy syn (D.Var   v)  = (S.typeof syn v handle e => raise e)
    | slotToTy syn (D.Expand _) = CPS.PTRt CPS.VPT (* FIXME *)
    | slotToTy syn (D.Code   f) = (S.typeof syn f handle e => raise e)
    | slotToTy syn D.Null       = CPS.PTRt CPS.VPT

  fun envszUnchecked ((_, _, web, syn): env, repr, v) =
    (case Web.webOfVar (web, v)
       of SOME w =>
           (case Web.content (web, w)
              of { polluted=true, kind=Web.Cont, ... } =>
                   [CPS.CNTt, bogusTy, bogusTy, bogusTy] (* FIXME: Magic number *)
               | { polluted=true, kind=Web.User, ... } =>
                   [bogusTy]
               | { polluted=false, defs, ... } =>
                   let val f = Vector.sub (defs, 0)
                       (* A known web has to have at least one function *)
                   in  map (slotToTy syn) (LCPS.FunMap.lookup (repr, f))
                   end)
        | NONE =>
           (case S.typeof syn v
              of CPS.CNTt => [CPS.CNTt, bogusTy, bogusTy, bogusTy]
               | ty => [ty]))

  fun envszChecked (env as (_, _, web, syn): env, repr, v) =
    let val w    = Web.webOfVar (web, v)
        val tys  = envszUnchecked (env, repr, v)
        val size = List.length tys
        fun sz f = List.length (LCPS.FunMap.lookup (repr, f))
    in  case w
          of NONE => tys
           | SOME w =>
               let val sizes = Vector.map sz (Web.defs (web, w))
               in  if Vector.all (fn s => s = size) sizes then
                     tys
                   else
                     (Web.dump web; raise Fail "Web constraint failed")
               end
    end

  val envsz = envszChecked

  (* fun tyOfEnv (ctx, env) : CPS.cty = *)
  (*   let val (_, D.T { heap, ... }) = *)

  val _ = slotToVar : D.slot -> CPS.lvar
  val _ = slotToVal : C.t -> D.slot -> CPS.value

  fun buildAccessMap (env: env, f: LCPS.function) : path LV.Map.map =
    let val (ctx, D.T { repr, heap, ... }, _, _) = env
        val roots  = LCPS.FunMap.lookup (repr, f)
        val insert = LV.Map.insertWith mergePath
        fun nexts (e, Path { base, selects }, todo) =
          (case EnvID.Map.find (heap, e)
             of SOME (D.Record slots) =>
                  List.foldli (fn (i, s, todo) =>
                    ((s, Path { base=base, selects=selects@[i] }) :: todo))
                    todo slots
              | SOME (D.RawBlock (vars, _)) =>
                  List.foldli (fn (i, v, todo) =>
                    ((D.Var v, Path { base=base, selects=selects@[i] })::todo))
                    todo vars
              | NONE => raise Fail "nexts")
        fun dfs ([], access) = access
          | dfs ((s, path) :: todo, access) =
              (case s
                 of D.Var v => dfs (todo, insert (access, v, path))
                  | D.Expand (v, i) =>
                      dfs ((C.expansionOf (ctx, v, i), path) :: todo,
                           access)
                  | D.EnvID e =>
                      dfs (nexts (e, path, todo),
                           insert (access, varOfEnv e, path))
                  | D.Null => dfs (todo, access)
                  | D.Code _ => dfs (todo, access))
        val names = map slotToVar (C.protocolOf (ctx, #2 f))
        val slots = LCPS.FunMap.lookup (repr, f)
        val bases =
          ListPair.foldl (fn (name, slot, bases) =>
            (slot, Path { base=name, selects=[] }) :: bases) [] (names, slots)
    in  dfs (bases, LV.Map.empty)
    end

  fun expandval (env: env, values: CPS.value list) : CPS.value list =
    let val (ctx, _, _, _) = env
        fun cvt (CPS.VAR v) = map (slotToVal ctx) (C.protocolOf (ctx, v))
          | cvt value       = [value]
    in  List.concatMap cvt values
    end

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
        val (fields, recKind) =
          (case object
             of D.Record slots => (map (slotToVal ctx) slots, CPS.RK_ESCAPE)
              | D.RawBlock (vs, rk) => (map CPS.VAR vs, rk))
        val (hdr, env as (ctx, dec, web, syn)) = fixaccess (env, fields)
        val name = varOfEnv e
        val fields = map (fn f => (LCPS.mkLabel (), f, CPS.OFFp 0)) fields
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
              let val tys = envsz (env, repr, x)
                  val (names, tys) = dupN (x, tys)
                  val ctx = C.addProtocol (ctx, x, map D.Var names)
              in  (names @ args, tys @ ts, ctx)
              end
        val (args, tys, ctx) = ListPair.foldr expand ([], [], ctx) (args, tys)
    in  (args, tys, (ctx, dec, web, syn))
    end

  fun needLinkReg (web, w) =
    let val { defs, uses, polluted, kind } = W.content (web, w)
    in  if not polluted andalso Vector.length defs = 1 then
          false
        else
          true
    end

  fun formalArg (name, ctx, D.Var v) = v
    | formalArg (name, ctx, D.Expand (v, i)) =
        formalArg (name, ctx, C.expansionOf (ctx, v, i))
    | formalArg (name, ctx, D.EnvID _) = freshLV name
    | formalArg (name, ctx, D.Code v) = v
    | formalArg (name, ctx, D.Null) = freshLV name

  fun closefun (env: env, names) (f as (fk, name, args, tys, body)) =
    let val (ctx, dec as D.T {repr, ...}, web, syn) = env
        val reprs = LCPS.FunMap.lookup (repr, f)
        val (envs, envtys) =
          ListPair.unzipMap (fn s => (formalArg (name, ctx, s), slotToTy syn s))
                            reprs
        val envslots = map D.Var envs
        val ctx =
          List.foldl (fn (name, ctx) => C.addProtocol (ctx, name, envslots))
            ctx names
        val env = (ctx, dec, web, syn)
        val accessMap = buildAccessMap (env, f)
        val env = (C.newContext (ctx, accessMap), dec, web, syn)
        val (args, tys, env) = expandargs (env, args, tys)
        (* LINK *)
        val (args, tys) = (freshLV name :: envs @ args, bogusTy :: envtys @ tys)
        val () = app print ["IN FUNCTION ", LV.lvarName name, "\n"]
        val () = C.dump (#1 env)
        val () = print "\n"
    in  (fk, name, args, tys, close (env, body))
    end
  and close (env, cexp as LCPS.FIX (label, bindings, exp)) =
        let val group = G.fromExp cexp
            val D.T { allo, repr, ... } = #2 env
            val envs  = Option.getOpt (G.Map.find (allo, group), [])
            val bindings = map (closefun (env, map #2 bindings)) bindings
            val (allocateHdr, env) = allocate (env, envs)
            val env = foldl (fn (f, (ctx, env, syn, web)) =>
              (C.addProtocol (ctx, #2 f, LCPS.FunMap.lookup (repr, f)), env,
               syn, web)) env bindings
            val () = app print ["AFTER FIX ", String.concatWithMap ","
            (LV.lvarName o #2) bindings, "\n"]
            val () = C.dump (#1 env)
            val () = print "\n"
        in  LCPS.FIX (label, bindings, allocateHdr (close (env, exp)))
        end
    | close (env as (ctx, dec, web, syn), LCPS.APP (label, f, args)) =
        let val args = expandval (env, args)
            val (hdr, env) = fixaccess (env, args)
            val mklab = LCPS.mkLabel
            val (ty, { defs, uses, polluted, kind }) =
              (case f
                 of CPS.VAR v =>
                      (case W.webOfVar (web, v)
                         of SOME w =>
                              (S.typeof syn v, W.content (web, w))
                          | NONE =>
                              (S.typeof syn v,
                               { defs= #[], uses= #[],
                                 polluted=true, kind=W.User }))
                  | _ =>
                      (bogusTy,
                       { defs= #[], uses= #[], polluted=true, kind=W.User }))
        in  if polluted then
              let val l = LV.mkLvar ()
                  val (hdr', env) = fixaccess1 (env, f)
                  val call =
                    LCPS.SELECT (mklab (), 0, f, l, ty,
                      (LCPS.APP (label, CPS.VAR l, CPS.VAR l::f::args)))
              in  hdr (hdr' call)
              end
            else
              let val (f, envs) = valOf (List.getItem (expandval (env, [f])))
                  val (hdr', env) = fixaccess (env, f :: envs)
              in  hdr (hdr' (LCPS.APP (label, f, envs @ args)))
              end
        end
    | close (env, LCPS.RECORD (label, rk, fields, x, exp)) =
        let val (hdr, env) = fixaccess (env, map #2 fields)
        in  hdr (LCPS.RECORD (label, rk, fields, x, close (env, exp)))
        end
    | close (env, LCPS.SELECT (label, i, v, x, ty, exp)) =
        let val (hdr, env) = fixaccess1 (env, v)
        in  hdr (LCPS.SELECT (label, i, v, x, ty, close (env, exp)))
        end
    | close (env, LCPS.OFFSET _) = raise Fail "Offset"
    | close (env, LCPS.SWITCH (label, v, x, exps)) =
        let val (hdr, env) = fixaccess1 (env, v)
        in  hdr (LCPS.SWITCH (label, v, x, map (fn e => close (env, e)) exps))
        end
    | close (env, LCPS.BRANCH (label, br, args, x, exp1, exp2)) =
        let val (hdr, env) = fixaccess (env, args)
        in  hdr (LCPS.BRANCH (label, br, args, x,
                   close (env, exp1), close (env, exp2)))
        end
    | close (env, LCPS.SETTER (label, st, args, exp)) =
        let val (hdr, env) = fixaccess (env, args)
        in  hdr (LCPS.SETTER (label, st, args, close (env, exp)))
        end
    | close (env, LCPS.LOOKER (label, lk, args, x, ty, exp)) =
        let val (hdr, env) = fixaccess (env, args)
        in  hdr (LCPS.LOOKER (label, lk, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.ARITH (label, ar, args, x, ty, exp)) =
        let val (hdr, env) = fixaccess (env, args)
        in  hdr (LCPS.ARITH (label, ar, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.PURE (label, pr, args, x, ty, exp)) =
        let val (hdr, env) = fixaccess (env, args)
        in  hdr (LCPS.PURE (label, pr, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.RCC (label, b, name, ty, args, rets, exp)) =
        let val (hdr, env) = fixaccess (env, args)
        in  hdr (LCPS.RCC (label, b, name, ty, args, rets, close (env, exp)))
        end

  fun transform ((fk, name, args, tys, body): LCPS.function, dec, web, syn) =
    let val ctx = C.initial ()
        val (ctx, args, tys) =
          (case (args, tys)
             of (ret::args, CPS.CNTt::tys) =>
                  let val link = freshLV name
                      val rets = freshNLV (name, 4)
                      val ctx = C.addProtocol (ctx, ret, map D.Var rets)
                  in  (ctx, link :: rets @ args,
                            bogusTy :: (map (fn _ => bogusTy) rets) @ tys)
                  end
              | _ => raise Fail "no return in top level")
          val () = print (Int.toString (List.length args) ^ "\n")
          val () = print (Int.toString (List.length tys) ^ "\n")
         val env = (ctx, dec, web, syn)
    in  (fk, name, args, tys, close (env, body))
    end
end
