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
  fun freshNLv (lvar, n) = List.tabulate (n, fn _ => freshLV lvar)

  structure Context :> sig
    type t

    val newContext : path LV.Map.map -> t

    val addProtocol : t * LCPS.lvar * D.slot list -> t
    val addInScope : t * LCPS.lvar -> t

    val protocolOf : t * LCPS.lvar -> D.slot list
    val expansionOf : t * LCPS.lvar * int -> D.slot
    val isInScope : t * LCPS.lvar -> bool
    val pathOf : t * LCPS.lvar -> path

    val dump : t -> unit
  end = struct
    datatype t = T of {
      access: path LV.Map.map,
      protocol: D.slot list LV.Map.map,
      inscope: LV.Set.set
    }

    fun newContext access =
      T { access=access, protocol=LV.Map.empty, inscope=LV.Set.empty }

    fun addProtocol (T {access, protocol, inscope}, v, slots) =
      T { access=access, protocol=LV.Map.insert (protocol, v, slots),
          inscope=inscope }

    fun addInScope (T {access, protocol, inscope}, v) =
      T { access=access, protocol=protocol, inscope=LV.Set.add (inscope, v) }

    fun protocolOf (T {protocol, ...}, v) =
      case LV.Map.find (protocol, v)
        of SOME slots => slots
         | NONE => raise Fail ("No protocol for " ^ LV.lvarName v)

    fun expansionOf (t, v, i) =
      let val proto = protocolOf (t, v)
      in  List.sub (proto, i)
          handle Subscript =>
          raise Fail (concat ["Invalid expansion #", Int.toString i, " of ",
                              LV.lvarName v])
      end

    fun isInScope (T {inscope, ...}, v) =
      LV.Set.member (inscope, v)

    fun pathOf (T {access, ...}, v) =
      case LV.Map.find (access, v)
        of SOME path => path
         | NONE => raise Fail (concat [LV.lvarName v, " is not in paths"])

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
    | slotToTy syn (D.Var   v)  = S.typeof syn v
    | slotToTy syn (D.Expand _) = CPS.PTRt CPS.VPT (* FIXME *)
    | slotToTy syn (D.Code   f) = S.typeof syn f
    | slotToTy syn D.Null       = CPS.PTRt CPS.VPT

  fun envszUnchecked ((_, _, web, syn): env, repr, v) =
    let val w = Web.webOfVar (web, v)
    in  case Web.content (web, w)
          of { polluted=true, kind=Web.Cont, ... } =>
               [CPS.CNTt, bogusTy, bogusTy, bogusTy] (* FIXME: Magic number *)
           | { polluted=true, kind=Web.User, ... } =>
               [bogusTy]
           | { polluted=false, defs, ... } =>
               let val f = Vector.sub (defs, 0)
                          (* A known web has to have at least one function *)
               in  map (slotToTy syn) (LCPS.FunMap.lookup (repr, f))
               end
    end

  fun envszChecked (env as (_, _, web, syn): env, repr, v) =
    let val w    = Web.webOfVar (web, v)
        val tys  = envszUnchecked (env, repr, v)
        val size = List.length tys
        fun sz f = List.length (LCPS.FunMap.lookup (repr, f))
        val sizes = Vector.map sz (Web.defs (web, w))
    in  if Vector.all (fn s => s = size) sizes then
          tys
        else
          (Web.dump web; raise Fail "Web constraint failed")
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
  fun pathToHdr (Path { base, selects }, name, cty) : header =
    let fun select [] v = raise Fail "Selecting empty"
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
        fun dupN (name, tys) =
          ListPair.unzipMap (fn ty => (freshLV name, ty)) tys
        fun expand (x, ty, (args, ts, ctx)) =
              let val tys = envsz (env, repr, x)
                  val (names, tys) = dupN (x, tys)
                  val ctx = C.addProtocol (ctx, x, map D.Var names)
              in  (names @ args, tys @ ts, ctx)
              end
        val (args, tys, ctx) = ListPair.foldr expand ([], [], ctx) (args, tys)
    in  (args, tys, (ctx, dec, web, syn))
    end

  fun closefun (env: env, (fk, name, args, tys, body)) = raise Fail ""
  and close exp = raise Fail ""

  fun transform (cps, D.T {repr, allo, heap}, web, syn) = cps
end
