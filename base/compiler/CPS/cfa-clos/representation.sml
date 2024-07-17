functor ClosureRepFn(MachSpec : MACH_SPEC) :> sig

  type functions = { known: LabelledCPS.function list, unknown: bool }

  type t
  val initialize : { cps: LabelledCPS.function,
                     syn: SyntacticInfo.t,
                     lookup: LambdaVar.lvar -> functions option,
                     escape: LabelledCPS.function -> bool }
                   -> t
  val dumpGraph : t -> unit
end = struct
  structure LV   = LambdaVar
  structure LCPS = LabelledCPS
  structure Syn  = SyntacticInfo
  structure EnvID = IdentifierFn()

  type lvar = LCPS.lvar
  type env_id = EnvID.t

  type functions = { known: LabelledCPS.function list, unknown: bool }

  datatype convention = StandardFunction | StandardContinuation | Free

  datatype closure = Clos of {
    code: LCPS.function list,
    convention: convention,
    env: env_id
  }

  datatype info = Data of CPS.cty
                | Refl of closure
                | Env  of env_id
                | Flow of { known: closure list, unknown: bool }

  datatype env = Boxed of field list
               | Flat    of field list
               | Unboxed of field list
  withtype field = lvar * info

  datatype t = Repr of {
    envs: env EnvID.Tbl.hash_table,
    protocol: closure LCPS.FunTbl.hash_table
  }

  fun fieldsOf (Boxed fields | Flat fields | Unboxed fields) = fields
  fun mapEnv f =
    fn Boxed fields => Boxed (f fields)
     | Flat fields => Flat (f fields)
     | Unboxed fields => Unboxed (f fields)
  fun mapFields f = mapEnv (map f)

  exception Decision
  fun initialize {cps: LCPS.function, syn, lookup, escape} =
    let
      val envs = EnvID.Tbl.mkTable (256, Decision)
      val protocol = LCPS.FunTbl.mkTable (256, Decision)

      (* annotate all functions with flat protocol *)
      val insertProtocol = LCPS.FunTbl.insert protocol
      val insertEnv      = EnvID.Tbl.insert envs
      val unions = foldl LV.Set.union LV.Set.empty

      fun newEnv env =
        let val id = EnvID.new "" in insertEnv (id, env); id end

      fun makeEnv bindings =
        let val names = map #2 bindings
            val fv = unions (map (Syn.fv syn) bindings)
            val fv = LV.Set.subtractList (fv, names)
            (* flat *)
            fun info v = Data (Syn.typeof syn v)
            val fv = LV.Set.foldr (fn (v, l) => (v, info v) :: l) [] fv
            val env = newEnv (Boxed fv)
            fun conv (f as (kind, _, _, _, _)) =
              if escape f then
                (case kind
                   of (CPS.CONT | CPS.KNOWN_CONT) => StandardContinuation
                    | _ => StandardFunction)
              else
                Free
        in  app (fn f => insertProtocol (f,
                  Clos { code=bindings, convention=conv f, env=env }))
                bindings;
            app (exp o #5) bindings
        end

      and exp (LCPS.APP (_, _, _)) = ()
        | exp (LCPS.FIX (_, bindings, body)) = (makeEnv bindings; exp body)
        | exp (LCPS.SWITCH (_, _, _, es)) = app exp es
        | exp (LCPS.BRANCH (_, _, _, _, te, fe)) = (exp te; exp fe)
        | exp (LCPS.RECORD (_, _, _, name, e) |
               LCPS.SELECT (_, _, _, name, _, e) |
               LCPS.OFFSET (_, _, _, name, e) |
               LCPS.LOOKER (_, _, _, name, _, e) |
               LCPS.ARITH  (_, _, _, name, _, e) |
               LCPS.PURE   (_, _, _, name, _, e)) = (exp e)
        | exp (LCPS.SETTER (_, _, _, e)) = exp e
        | exp (LCPS.RCC    (_, _, _, _, _, returns, e)) = exp e

      fun lookupClosure f =
        (case LCPS.FunTbl.find protocol f
           of NONE => raise Fail ("lookupClosure " ^ LV.lvarName (#2 f))
            | SOME c => c)

      fun fixFlow env =
        let fun fix (v, info) =
              (case lookup v
                 of NONE => (v, info)
                  | SOME {known=[function], unknown=false} =>
                      if LV.same (#2 function, v) then
                        (v, Refl (lookupClosure function))
                      else
                        (v,
                         Flow { known=[lookupClosure function], unknown=false })
                  | SOME {known, unknown} =>
                      (v,
                       Flow { known=map lookupClosure known, unknown=unknown }))
        in  mapFields fix env
        end
      val () = exp (#5 cps)
      val envs = EnvID.Tbl.map fixFlow envs
    in
      Repr { envs=envs, protocol=protocol }
    end

  fun coalesceUnboxed (Repr {envs, protocol}) =
    let
      fun updateEnv (id', env) =
        let
          fun loop fields =
            let fun go (f as (v, Env id), (acc, changed)) =
                      if EnvID.same (id, id') then
                        raise Fail "Circularity"
                      else
                        (case EnvID.Tbl.lookup envs id
                           of Unboxed fields => (fields @ acc, true)
                            | _ => (f :: acc, changed))
                  | go (f as (v, Refl (Clos{env, code, convention})),
                        (acc, changed)) =
                      if EnvID.same (env, id') then
                        (f :: acc, changed)
                      else
                        (case EnvID.Tbl.lookup envs env
                           of Unboxed fields =>
                                let
                                  val clos' = Clos {env=id', code=code,
                                                    convention=convention}
                                in
                                  (fields @ (v, Refl clos') :: acc, true)
                                end
                            | _ => (f :: acc, changed))
                  | go (f, (acc, changed)) = (f :: acc, changed)
                val (fields, changed) = foldl go ([], false) fields
            in  if changed then loop fields else List.rev fields
            end
        in
          mapEnv loop env
        end
    in
      EnvID.Tbl.modifyi updateEnv envs
    end

  local open DotLanguage in
  fun dumpGraph (Repr {envs, protocol}) =
    let
      val strv = LV.lvarName
      fun pconv StandardFunction = "std"
        | pconv StandardContinuation = "cont"
        | pconv Free = "free"
      fun closureID (Clos {env, ...}) = "clo/" ^ EnvID.toString env
      fun closureN (clos as Clos {code, convention, env}) =
        let val names = map #2 code
            val label = concat ["Closure/", String.concatWithMap "," strv names,
                               "/", pconv convention, "/", EnvID.toString env]
        in  NODE (closureID clos, [("label", label), ("shape", "box")])
        end
      (* fun sfield (n, info) = *)
      (*   (case info *)
      (*      of Data ty => concat [strv n, CPSUtil.ctyToString cty] *)
      (*       | Refl cl => *)
      val envID = EnvID.toString
      fun envN (id, env) =
        let val kind = case env of Boxed _ => "box"
                                 | Flat _ => "flat" | Unboxed _ => "unboxed"
            val name = concat ["Env/", envID id, "/", kind]
        in  NODE (envID id, [("label", name), ("shape", "box")])
        end
      fun collectClo (clo as Clos {env, ...}, stmts) =
        let val node = closureN clo
            val edge = EDGE (envID env, closureID clo, [("arrowhead", "crow")])
        in  edge :: node :: stmts
        end
      fun collectEnv (id, env, stmts) =
        let val node = envN (id, env)
            val envid = envID id
            fun collectField ((n, info), stmts) =
              (case info
                 of Data ty =>
                      let val n = strv n
                          val label = n ^ CPSUtil.ctyToString ty
                      in  NODE (n, [("label", label), ("color", "gray")])
                          :: EDGE (n, envid, [])
                          :: stmts
                      end
                  | Refl clo => EDGE (closureID clo, envid, []) :: stmts
                  | Env id => EDGE (envID id, envid, []) :: stmts
                  | Flow {known, unknown} =>
                      let val n = strv n
                          val label =
                            if unknown then concat [n, "/unknown"] else n
                          fun collectEdges (clo, stmts) =
                            EDGE (closureID clo, n, [("style", "dashed")]) ::
                            stmts
                      in  NODE (n, [("label", label)])
                          :: EDGE (n, envid, [])
                          :: foldl collectEdges stmts known
                      end)
        in  foldl collectField (node :: stmts) (fieldsOf env)
        end
      val stmts = LCPS.FunTbl.fold collectClo [] protocol
      val stmts = EnvID.Tbl.foldi collectEnv stmts envs
      val dot = empty (true, "representation")
    in  dump (<+< (dot,
          [ATTR "rankdir=\"LR\"", ATTR "rank=source"] @ List.rev stmts))
    end
  end

end
