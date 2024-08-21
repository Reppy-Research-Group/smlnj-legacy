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

  datatype code = Direct of LCPS.function
                | Pointer of LCPS.lvar
                | Defun of LCPS.lvar * LCPS.function list

  datatype protocol = Protocol of {
    code: code,
    slots: D.slot list,
    pkg: LCPS.lvar option
  }

  fun slotsOfProtocol (Protocol { slots, ... }) = slots

  fun protocolToS (Protocol { code, slots, pkg }) =
    concat [codeToS code, "(", String.concatWithMap "," D.slotToString slots, "...)"]
  and codeToS (Direct f) = LV.lvarName (#2 f)
    | codeToS (Pointer p) = concat ["(*", pathToS p, ")"]
    | codeToS (Defun (p, fs)) = concat ["#", pathToS p]

  fun tagInt i =
    CPS.NUM { ival=IntInf.fromInt i, ty={ sz=Target.defaultIntSz, tag=true }}

  fun freshLV lvar = LV.dupLvar lvar
  fun freshNLV (lvar, n) = lvar :: List.tabulate (n - 1, fn _ => freshLV lvar)

  structure Context :> sig
    type t

    val initial    : unit -> t
    val newContext : t * path LV.Map.map -> t

    val addProtocol : t * LCPS.lvar * protocol -> t
    val addInScope : t * LCPS.lvar -> t

    val protocolOf  : t * LCPS.lvar -> protocol
    val protocolOf' : t * LCPS.lvar -> protocol option
    val expansionOf : t * LCPS.lvar * int -> D.slot
    val isInScope : t * LCPS.lvar -> bool
    val pathOf : t * LCPS.lvar -> path option

    val dump : t -> unit
  end = struct

    datatype t = T of {
      access: path LV.Map.map,
      protocol: protocol LV.Map.map,
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

    fun protocolOf' (T {protocol, ...}, v) = LV.Map.find (protocol, v)
         (* raise Fail ("No protocol for " ^ LV.lvarName v) *)

    fun protocolOf (ctx, v) =
      (case protocolOf' (ctx, v)
         of SOME p => p
          | NONE => raise Fail (LV.lvarName v ^ " is not a function "))

    fun expansionOf (t, v, i) =
      (case protocolOf' (t, v)
         of SOME (Protocol { code, slots, pkg }) =>
              (List.sub (slots, i)
               handle Subscript =>
               raise Fail (concat
                 ["Invalid expansion #", Int.toString i, " of ", LV.lvarName v,
                  ": [", String.concatWithMap "," D.slotToString slots, "]"]))
          | NONE => raise Fail (concat ["Invalid expansion: ", LV.lvarName v,
            " is not a function"]))

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
          p ["  ", LV.lvarName v, " --> [", protocolToS proto, "]\n"]
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

  (* envcp:
   * 1. polluted user: code is (#1).1
   * 2. polluted cont: code is #1
   * 3. singleton web: code is direct
   * 4. otherwise web: code is .1 if boxed, and #1 if unboxed
   *    FIXME: There really should be a way to communicate where the code is
   *    from the decision.
   *)

  fun envszUnchecked ((_, _, web, syn): env, repr, v) =
    (case Web.webOfVar (web, v)
       of SOME w =>
           (case Web.content (web, w)
              of { polluted=true, kind=Web.Cont, ... } =>
                   SOME [CPS.CNTt, bogusTy, bogusTy, bogusTy] (* FIXME: Magic number *)
               | { polluted=true, kind=Web.User, ... } =>
                   SOME [bogusTy]
               | { polluted=false, defs, ... } =>
                   let val f = Vector.sub (defs, 0)
                       (* A known web has to have at least one function *)
                   in  SOME (map (slotToTy syn) (LCPS.FunMap.lookup (repr, f)))
                   end)
        | NONE =>
           (case S.typeof syn v
              of CPS.CNTt => SOME [CPS.CNTt, bogusTy, bogusTy, bogusTy]
               | ty => NONE))

  fun envszChecked (env as (_, _, web, syn): env, repr, v) =
    let val w    = Web.webOfVar (web, v)
        val tys  = envszUnchecked (env, repr, v)
    in  case (w, tys)
          of (NONE, _) => tys
           | (_, NONE) => tys
           | (SOME w, SOME tys') =>
               let val size = List.length tys'
                   fun sz f = List.length (LCPS.FunMap.lookup (repr, f))
                   val sizes = Vector.map sz (Web.defs (web, w))
               in  if Vector.all (fn s => s = size) sizes then
                     tys
                   else
                     (Web.dump web; raise Fail "Web constraint failed")
               end
    end

  val envsz = envszChecked

  fun envcp ((_, _, web, syn): env, repr, sub, v) : code =
    (case Web.webOfVar (web, v)
       of SOME w =>
           (case Web.content (web, w)
              of { defs= #[f], ... } =>
                   Direct f
               | { polluted=true, kind=Web.Cont, ... } =>
                   (* [CPS.CNTt, bogusTy, bogusTy, bogusTy] *)
                   Pointer (Path {base=sub 0, selects=[]})
               | { polluted=true, kind=Web.User, ... } =>
                   (* [bogusTy] *)
                   Pointer (Path {base=sub 0, selects=[0]})
               | { polluted=false, defs, ... } =>
                   let val f = Vector.sub (defs, 0)
                       val slots = LCPS.FunMap.lookup (repr, f)
                   in  case slots
                         of [] =>
                              raise Fail "No code ptr for non-singleton web"
                          | [D.EnvID _] =>
                              Pointer (Path {base=sub 0, selects=[0]})
                          | (D.Code _::_) =>
                              Pointer (Path {base=sub 0, selects=[]})
                          | _ =>
                              raise Fail "Code ptr is not the first"
                   end)
        | NONE =>
           (case S.typeof syn v
              of CPS.CNTt =>
                   Pointer (Path {base=sub 0, selects=[]})
               | _ =>
                   Pointer (Path {base=sub 0, selects=[0]})))

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
        val Protocol { slots, ... } = C.protocolOf (ctx, #2 f)
        val names = map slotToVar slots
        val slots = LCPS.FunMap.lookup (repr, f)
        val bases =
          ListPair.foldl (fn (name, slot, bases) =>
            (slot, Path { base=name, selects=[] }) :: bases) [] (names, slots)
    in  dfs (bases, LV.Map.empty)
    end

  fun expandval (env: env, values: CPS.value list) : CPS.value list =
    let val (ctx, _, _, _) = env
        fun cvt (CPS.VAR v) =
              (case C.protocolOf' (ctx, v)
                 of SOME (Protocol { slots, ... }) => map (slotToVal ctx) slots
                  | NONE => [CPS.VAR v])
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
          (case envsz (env, repr, x)
             of NONE => (* this is not a function *)
                  (x :: args, ty :: ts, ctx)
              | SOME tys =>
                  let val (names, tys) = dupN (x, tys)
                      fun sub i = List.sub (names, i)
                      val codeptr = envcp (env, repr, sub, x)
                      val p = Protocol { code=codeptr, slots=map D.Var names,
                                         pkg=NONE }
                      val ctx = C.addProtocol (ctx, x, p)
                  in  (names @ args, tys @ ts, ctx)
                  end)
        val (args, tys, ctx) = ListPair.foldr expand ([], [], ctx) (args, tys)
    in  (args, tys, (ctx, dec, web, syn))
    end

  fun addvar ((ctx, dec, web, syn): env, name: CPS.lvar, CPS.FUNt): env =
        (* CNT is not going to be here *)
        let val code = 
              (case Web.webOfVar (web, name)
                 of SOME w =>
                      (case Web.content (web, w)
                         of { defs= #[f], ... } =>
                              Direct f
                          | _ =>
                              Pointer (Path {base=name, selects=[0]}))
                  | NONE => Pointer (Path {base=name, selects=[0]}))
            (* The slot really should be an EnvID *)
            val p = Protocol { code=code, slots=[D.Var name], pkg=NONE }
            val ctx = C.addProtocol (ctx, name, p)
        in  (ctx, dec, web, syn)
        end
   | addvar (env, _, _) = env

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

  fun closefun (env: env, functions) (f as (fk, name, args, tys, body)) =
    let val (ctx, dec as D.T {repr, ...}, web, syn) = env
        val reprs = LCPS.FunMap.lookup (repr, f)
        val (envs, envtys) =
          ListPair.unzipMap (fn s => (formalArg (name, ctx, s), slotToTy syn s))
                            reprs
        val envslots = map D.Var envs
        fun addproto (f, ctx) =
          let val p = Protocol { code=Direct f, slots=envslots, pkg=NONE }
          in  C.addProtocol (ctx, #2 f, p)
          end
        val ctx = List.foldl addproto ctx functions
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
            val bindings = map (closefun (env, bindings)) bindings
            val (allocateHdr, env) = allocate (env, envs)
            fun addproto (f, (ctx, env, syn, web)) =
              let val slots = LCPS.FunMap.lookup (repr, f)
                  val p = Protocol { code=Direct f, slots=slots, pkg=NONE }
              in  (C.addProtocol (ctx, #2 f, p), env, syn, web)
              end
            val env = foldl addproto env bindings
            val () = app print ["AFTER FIX ", String.concatWithMap ","
            (LV.lvarName o #2) bindings, "\n"]
            val () = C.dump (#1 env)
            val () = print "\n"
        in  LCPS.FIX (label, bindings, allocateHdr (close (env, exp)))
        end
    | close (env as (ctx, dec, web, syn), LCPS.APP (label, CPS.VAR f, args)) =
        let val args = expandval (env, args)
            val (hdr, env) = fixaccess (env, args)
            val mklab = LCPS.mkLabel
            val Protocol { code, slots, ... } = C.protocolOf (ctx, f)
            val slots = map (slotToVal ctx) slots
            val (hdr', env) = fixaccess (env, slots)
            val args = slots @ args
        in  case code
              of Direct f =>
                   hdr (hdr' (LCPS.APP (mklab (), CPS.LABEL (#2 f), CPS.LABEL (#2 f) :: args)))
               | Pointer (Path {base, selects=[]}) =>
                   hdr (hdr' (LCPS.APP (mklab (), CPS.VAR base, args)))
               | Pointer p =>
                   let val name = freshLV f
                       val ty = S.typeof syn f
                       val hdr'' = pathToHdr (SOME p, name, ty)
                       val call = LCPS.APP (mklab (), CPS.VAR name, CPS.VAR name :: args)
                   in  hdr (hdr' (hdr'' call))
                   end
               | Defun _ => raise Fail "unimp"
        end
    | close (env as (ctx, dec, web, syn), LCPS.APP (label, _, args)) =
        raise Fail "calling non-var functions"
            (* val (ty, { defs, uses, polluted, kind }) = *)
            (*   (case f *)
            (*      of CPS.VAR v => *)
            (*           (case W.webOfVar (web, v) *)
            (*              of SOME w => *)
            (*                   (S.typeof syn v, W.content (web, w)) *)
            (*               | NONE => *)
            (*                   (S.typeof syn v, *)
            (*                    { defs= #[], uses= #[], *)
            (*                      polluted=true, kind=W.User })) *)
            (*       | _ => *)
            (*           (bogusTy, *)
            (*            { defs= #[], uses= #[], polluted=true, kind=W.User })) *)
        (* in  if polluted then *)
            (*   let val l = LV.mkLvar () *)
            (*       val (hdr', env) = fixaccess1 (env, f) *)
            (*       val call = *)
            (*         LCPS.SELECT (mklab (), 0, f, l, ty, *)
            (*           (LCPS.APP (label, CPS.VAR l, CPS.VAR l::f::args))) *)
            (*   in  hdr (hdr' call) *)
            (*   end *)
            (* else *)
            (*   let val (f, envs) = valOf (List.getItem (expandval (env, [f]))) *)
            (*       val (hdr', env) = fixaccess (env, f :: envs) *)
            (*   in  hdr (hdr' (LCPS.APP (label, f, envs @ args))) *)
            (*   end *)
        (* end *)
    | close (env, LCPS.RECORD (label, rk, fields, x, exp)) =
        let val (hdr, env) = fixaccess (env, map #2 fields)
        in  hdr (LCPS.RECORD (label, rk, fields, x, close (env, exp)))
        end
    | close (env, LCPS.SELECT (label, i, v, x, ty, exp)) =
        let val (hdr, env) = fixaccess1 (env, v)
            val env = addvar (env, x, ty)
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
            val env = addvar (env, x, ty)
        in  hdr (LCPS.LOOKER (label, lk, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.ARITH (label, ar, args, x, ty, exp)) =
        let val (hdr, env) = fixaccess (env, args)
            val env = addvar (env, x, ty)
        in  hdr (LCPS.ARITH (label, ar, args, x, ty, close (env, exp)))
        end
    | close (env, LCPS.PURE (label, pr, args, x, ty, exp)) =
        let val (hdr, env) = fixaccess (env, args)
            val env = addvar (env, x, ty)
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
                      val clos = freshLV name
                      val rets = freshNLV (ret, 4)
                      val rettys = [CPS.CNTt, bogusTy, bogusTy, bogusTy]
                      val p = Protocol {
                        code=Pointer (Path {base=ret, selects=[]}),
                        slots=D.Var ret :: map D.Var (List.tl rets),
                        pkg=NONE} 
                      val ctx = C.addProtocol (ctx, ret, p)
                  in  (ctx, link::clos::rets@args, bogusTy::bogusTy::rettys@tys)
                  end
              | _ => raise Fail "no return in top level")
          val () = print (Int.toString (List.length args) ^ "\n")
          val () = print (Int.toString (List.length tys) ^ "\n")
         val env = (ctx, dec, web, syn)
    in  (fk, name, args, tys, close (env, body))
    end
end
