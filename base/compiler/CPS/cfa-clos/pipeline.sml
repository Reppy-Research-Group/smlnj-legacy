structure ClosureDecisionPipeline :> sig
  (* val initial : LabelledCPS.function * SyntacticInfo.t -> ClosureDecision.t *)
  (* val share : ClosureDecision.t * SyntacticInfo.t * ControlFlow.block * SharingAnalysis.result *)
  (*           -> ClosureDecision.t *)

  val pipeline : LabelledCPS.function * SyntacticInfo.t * SharingAnalysis.result
  * ControlFlow.funtbl -> ClosureDecision.t
end = struct
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo
  structure SA = SharingAnalysis
  structure CF = ControlFlow
  structure PackID = SA.PackID

  fun initial (cps: LCPS.function, syn: S.t) =
    let fun collect syn (group, (repr, allo, heap)) =
          let val functions = S.groupFun syn group
              val fv = LV.Map.listKeys (S.groupFV syn group)
              val slots = map (fn v => D.Var (v, S.typeof syn v)) fv
          in  case functions
                of #[f] =>
                     let val envid = EnvID.new ()
                         val heap  =
                           EnvID.Map.insert (heap, envid,
                             D.Record (D.Code f :: slots))
                         val repr  =
                           LCPS.FunMap.insert (repr, f, D.Closure {
                             code=D.SelectFrom { env=0, selects=[0] },
                             env=D.Boxed envid
                           })
                         val allo  =
                           Group.Map.insert (allo, group, [envid])
                     in  (repr, allo, heap)
                     end
                 | _ =>
                     let val shareEnv = EnvID.new ()
                         val heap =
                           EnvID.Map.insert (heap, shareEnv, D.Record slots)
                         val (repr, heap, envs) =
                           Vector.foldl (fn (f, (repr, heap, envs)) =>
                             let val env = EnvID.new ()
                                 val heap =
                                   EnvID.Map.insert (heap, env,
                                     D.Record [D.Code f, D.EnvID shareEnv])
                                 val repr =
                                   LCPS.FunMap.insert (repr, f,
                                     D.Closure {
                                       code=D.SelectFrom { env=0, selects=[0] },
                                       env=D.Boxed env
                                     })
                             in  (repr, heap, env :: envs)
                             end
                           ) (repr, heap, [shareEnv]) functions
                         val allo = Group.Map.insert (allo, group, rev envs)
                     in  (repr, allo, heap)
                     end
          end
        val (repr, allo, heap) =
          Vector.foldl (collect syn)
            (LCPS.FunMap.empty, Group.Map.empty, EnvID.Map.empty)
            (S.groups syn)
    in  D.T { repr=repr, allo=allo, heap=heap }
    end

  fun prependAllo (allo: D.allo, group: Group.t, envids': EnvID.t list) =
    (case Group.Map.find (allo, group)
       of SOME envids => Group.Map.insert (allo, group, envids' @ envids)
        | NONE => Group.Map.insert (allo, group, envids'))

  (* NOTE: it assumes all vars to replaced are in the same environment *)
  fun replaceVars (object, vars: LV.Set.set, packs: EnvID.t list): D.object =
    (case object
       of D.Record slots =>
            let fun isTarget (D.Var (v, _)) = LV.Set.member (vars, v)
                  | isTarget (D.Expand (v, _, _)) = LV.Set.member (vars, v)
                  | isTarget _ = false
                val slots =
                  List.filter (not o isTarget) slots @ map D.EnvID packs
            in  D.Record slots
            end
        | D.RawBlock _ => raise Fail "No raw blocks at this stage")

  fun share (
    D.T {repr, allo, heap},
    syn: S.t,
    entry: CF.block,
    funtbl: CF.funtbl,
    (grpTbl, packTbl): SA.result
  ) : D.t =
    let val envidTbl = PackID.Tbl.map (fn _ => EnvID.new ()) packTbl
        val envOfPack = PackID.Tbl.lookup envidTbl
        val entryOf = LCPS.FunTbl.lookup funtbl
        fun shares (grp, functions, availPacks, allo, heap) =
          let val SA.Pack { packs, ... } = Group.Tbl.lookup grpTbl grp
              val packs = PackID.Set.listItems packs
              val allocated = Group.Map.lookup (allo, grp)

              val replacing = foldl (fn (pack, vars) =>
                  let val SA.Pack { fv, ... } = PackID.Tbl.lookup packTbl pack
                  in  LV.Set.union (vars, fv)
                  end
                ) LV.Set.empty packs

              val packEnvs = map envOfPack packs

              val heap = foldl (fn (envid, heap) =>
                  let val object = EnvID.Map.lookup (heap, envid)
                      val object = replaceVars (object, replacing, packEnvs)
                  in  EnvID.Map.insert (heap, envid, object)
                  end
                ) heap allocated

              (* Split it into received packs and packs to create. *)
              val (received, allocate) =
                List.partition (fn p => PackID.Set.member (availPacks, p)) packs

              val allo = prependAllo (allo, grp, map envOfPack allocate)
              val heap = foldl (fn (p, heap) =>
                  let val env = envOfPack p
                      val SA.Pack { packs, loose, ... } =
                        PackID.Tbl.lookup packTbl p
                      val () = if PackID.Set.isEmpty packs then () else
                        raise Fail "TODO: non empty shared packs"
                      val slots = LV.Set.foldr (fn (v, slots) =>
                          D.Var (v, S.typeof syn v) :: slots
                        ) [] loose
                  in  EnvID.Map.insert (heap, env, D.Record slots)
                  end
                ) heap allocate

              (* NOTE: assumes no flattening has taken place *)
          in  (PackID.Set.addList (availPacks, allocate), allo, heap)
          end
        fun walk (CF.Block {term, fix, ... }, availPacks, allo: D.allo, heap:
          D.heap) =
          let val (availPacks, allo, heap) =
                foldl (fn ((grp, fs), (availPacks, allo, heap)) =>
                  let val (availPacks, allo, heap) =
                        shares (grp, fs, availPacks, allo, heap)
                      val (allo, heap) =
                        foldl (fn (f, (allo, heap)) =>
                          walk (entryOf f, availPacks, allo, heap)
                        ) (allo, heap) fs
                  in  (availPacks, allo, heap)
                  end
                ) (availPacks, allo, heap) fix
          in  case term
                of CF.Branch (_, _, b1, b2, _) =>
                     let val (allo, heap) = walk (b1, availPacks, allo, heap)
                     in  walk (b2, availPacks, allo, heap)
                     end
                 | CF.Switch blocks =>
                     foldl (fn ((b, _), (allo, heap)) =>
                       walk (b, availPacks, allo, heap)
                     ) (allo, heap) blocks
                 | _ => (allo, heap)
          end
        val (allo, heap) = walk (entry, PackID.Set.empty, allo, heap)
    in  D.T { repr=repr, allo=allo, heap=heap }
    end

  fun pipeline (
    cps: LCPS.function,
    syn: S.t,
    shr: SA.result,
    funtbl: CF.funtbl
  ): D.t =
    let val decision = initial (cps, syn)
        val decision =
          share (decision, syn, LCPS.FunTbl.lookup funtbl cps, funtbl, shr)
        val () = ClosureDecision.dump (decision, syn)
    in  decision
    end
end
