structure ClosureDecisionPipeline :> sig
  val pipeline : LabelledCPS.function
               * SyntacticInfo.t
               * Web.t
               * SharingAnalysis.result
               * ControlFlow.funtbl
              -> ClosureDecision.t
end = struct
  structure CF = ControlFlow
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure PackID = SharingAnalysis.PackID
  structure S = SyntacticInfo
  structure SA = SharingAnalysis
  structure W = Web

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

  type rewriting = D.t -> D.t

  fun share (
    syn: S.t,
    entry: CF.block,
    funtbl: CF.funtbl,
    (grpTbl, packTbl): SA.result
  ) (D.T {repr, allo, heap}) : D.t =
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

  fun flattenEscapingClosures (
    syn: S.t,
    web: W.t
  ) (D.T {repr, allo, heap}) =
    (* Step 1: allocate a bunch of NIL for all escaping closures' reprs. *)
     let fun isEscapingCont f =
           let val w = W.webOfFun (web, f)
           in  W.kind (web, w) = W.Cont
               (* andalso W.polluted (web, w) = true *)
           end

         fun codePtr (D.SelectFrom { env=0, selects=[0] }, D.Boxed e) =
               let val object = EnvID.Map.lookup (heap, e)
               in  case object
                     of D.Record (D.Code f :: _) => #2 f
                      | _ => raise Fail "impossible"
               end
           | codePtr _ = raise Fail "unimp"

         fun expandRepr (f, repr) =
           let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
               val (code, env) =
                 (case env
                    of D.Boxed e =>
                         let val codep = codePtr (code, env)
                         in  (D.Pointer codep,
                              D.Flat [D.EnvID e, D.Null, D.Null])
                         end
                     | D.Flat slots =>
                         let val length = List.length slots
                             val diff   = 3 - length
                         in  if diff > 0 then
                               (code,
                                D.Flat (slots @ List.tabulate (diff, fn _ => D.Null)))
                             else if diff = 0 then
                               (code, env)
                             else
                               raise Fail "impossible"
                         end)
            in  LCPS.FunMap.insert (repr, f, D.Closure { code=code, env=env })
           end

         val repr = S.foldF syn (fn (f, repr) =>
             if isEscapingCont f then expandRepr (f, repr) else repr
           ) repr

         (* Step 2: replace all variables in the heap with the expansions *)
         (* Do not need to go through reprs because they don't have expansions
          * yet *)

         fun isContVar (v, CPS.CNTt) = true
           | isContVar _ = false

         val bogusTy = CPSUtil.BOGt
         fun expandObject (D.Record slots) =
               let fun go [] = []
                     | go ((x as D.Var (v, ty))::xs) =
                         if isContVar (v, ty) then
                           D.Var (v, ty)
                           :: List.tabulate (3, fn i => D.Expand (v, i, bogusTy))
                           @ go xs
                         else
                           x :: go xs
                     | go (x :: xs) = x :: go xs
               in  D.Record (go slots)
               end
           | expandObject obj = obj
         val heap = EnvID.Map.map expandObject heap
     in  D.T { repr=repr, allo=allo, heap=heap }
     end

  fun isFloatTy (CPS.FLTt _) = true
    | isFloatTy _ = false

  fun isUntaggedIntTy (CPS.NUMt { tag, ... }) = not tag
    | isUntaggedIntTy _ = false

  fun segregateMLValues (D.T { repr, allo, heap }): D.t =
    let fun partitionSlots slots =
          let fun go ([], slots, ints, flts) =
                    (rev slots, rev ints, rev flts)
                | go (x :: xs, slots, ints, flts) =
                    (case x
                       of D.Var (v, ty) =>
                            if isUntaggedIntTy ty then
                              go (xs, slots, v :: ints, flts)
                            else if isFloatTy ty then
                              go (xs, slots, ints, v :: flts)
                            else
                              go (xs, x :: slots, ints, flts)
                        | _ => go (xs, x :: slots, ints, flts))
          in  go (slots, [], [], [])
          end
        fun maybeAllocRaw ([], heap, _) = (NONE, heap)
          | maybeAllocRaw (xs, heap, kind) =
              let val env = EnvID.new ()
                  val obj = D.RawBlock (xs, kind)
                  val heap = EnvID.Map.insert (heap, env, obj)
              in  (SOME env, heap)
              end
        val concatPartial = List.mapPartial Fn.id
        fun scan (env, heap): EnvID.t list * D.heap =
          let val object = EnvID.Map.lookup (heap, env)
          in  case object
                of D.RawBlock _ => ([], heap)
                 | D.Record slots =>
                     let val (slots, ints, flts) = partitionSlots slots
                         val (intEnv, heap) =
                           maybeAllocRaw (ints, heap, CPS.RK_RAWBLOCK)
                         val (fltEnv, heap) =
                           maybeAllocRaw (flts, heap, CPS.RK_RAW64BLOCK)
                         val envs =
                           List.mapPartial (Option.map D.EnvID) [intEnv, fltEnv]
                         val heap =
                           EnvID.Map.insert (heap, env, D.Record (slots @ envs))
                     in  (concatPartial [intEnv, fltEnv], heap)
                     end
          end
        val (allo, heap) = Group.Map.foldli (fn (grp, envs, (allo, heap)) =>
            let val (envs, heap) = foldr (fn (env, (envs, heap)) =>
                    let val (additional, heap) = scan (env, heap)
                    in  (additional @ (env :: envs), heap)
                    end
                  ) ([], heap) envs
                val allo = Group.Map.insert (allo, grp, envs)
            in  (allo, heap)
            end
          ) (allo, heap) allo
    in  D.T { repr=repr, allo=allo, heap=heap }
    end

  val _ = initial : LCPS.function * S.t -> D.t
  val _ = share   : S.t * CF.block * CF.funtbl * SA.result -> rewriting
  val _ = flattenEscapingClosures : S.t * W.t -> rewriting
  val _ = segregateMLValues : rewriting

  infix 2 >>>
  fun f >>> g = fn x => g (f x)

  (* TODO: clear out zero sized fields *)

  fun pipeline (
    cps: LCPS.function,
    syn: S.t,
    web: W.t,
    shr: SA.result,
    funtbl: CF.funtbl
  ): D.t =
    let val process =
              initial
          >>> share (syn, LCPS.FunTbl.lookup funtbl cps, funtbl, shr)
          >>> flattenEscapingClosures (syn, web)
          >>> segregateMLValues

        val decision = process (cps, syn)
        val () = ClosureDecision.dump (decision, syn)
    in  decision
    end
end
