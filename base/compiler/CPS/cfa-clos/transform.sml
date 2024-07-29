structure Transform :> sig
  val transform : LCPS.function * ClosureDecision.t * Web.t -> LCPS.function
end = struct
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo

  datatype path = Path of { base: LV.lvar, selects: int list }

  fun pathToS (Path {base, selects}) =
        concat (LV.lvarName base :: map (fn i => "." ^ Int.toString i) selects)

  fun pathMerge (Path { base=b1, selects=s1 }, Path { base=b2, selects=s2 }) =
    if List.length s1 <= List.length s2 then
      Path { base=b1, selects=s1 }
    else
      Path { base=b2, selects=s2 }

  fun tagInt i =
    CPS.NUM { ival=IntInf.fromInt i, ty={ sz=Target.defaultIntSz, tag=true }}

  fun slotToVal (D.EnvID e) = CPS.VAR (D.EnvID.unwrap e)
    | slotToVal (D.Var v) = CPS.VAR v
    | slotToVal (D.Code v) = CPS.LABEL v
    | slotToVal D.Null = tagInt 0

  fun freshLV lvar = LV.dupLvar lvar
  fun freshNLv (lvar, n) = List.tabulate (n, fn _ => freshLV lvar)

  fun envszUnchecked (web, repr, v) =
    let val w = Web.webOfVar (web, v)
    in  case Web.content (web, w)
          of { polluted=true, kind=Web.Cont, ... } =>
               3 (* FIXME: Magic number *)
           | { polluted=true, kind=Web.User, ... } =>
               1
           | { polluted=false, defs, ... } =>
               let val f = Vector.sub (defs, 0)
                          (* A known web has to have at least one function *)
               in  List.length (LCPS.FunMap.lookup (repr, f))
               end
    end

  fun envszChecked (web, repr, v) =
    let val w    = Web.webOfVar (web, v)
        val size = envszUnchecked (web, repr, v)
        fun sz f = List.length (LCPS.FunMap.lookup (repr, f))
        val sizes = Vector.map sz defs
    in  if Vector.all (fn s => s = size) sizes then
          size
        else
          (Web.dump web; raise Fail "Web constraint failed")
    end

  val envsz = envszChecked

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
      inscope: LV.Set.set,
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
        LV.Map.appi pprotocol access;
        p ["== InScope ==\n"];
        p ["[", cwm "," LV.lvarName inscope, "]"]
      end
  end

  type input = context * D.t

  val varOfEnv = EnvID.unwrap : EnvID.t -> LCPS.lvar

  fun buildAccessMap (input: input, f: LCPS.function) : path LV.Map.map =
    let val T { repr, heap, ... } = #2 input
        val roots  = LCPS.FunMap.lookup (repr, f)
        val insert = LV.Map.insertWith mergePath
        fun dfs ([], access) = access
          | dfs ((s, path) :: todo', access) =
              (case s
                 of Var v => dfs (insert (access, v, path))
                  | 

  fun transform (cps, D.T {repr, allo, heap}) = raise Fail ""
end
