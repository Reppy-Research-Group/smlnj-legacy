structure ClosureDecisionPipeline :> sig
  val pipeline : LabelledCPS.function
               * SyntacticInfo.t
               * Web.t
               * SharingAnalysis.result
               * ControlFlow.funtbl
               * ControlFlow.looptbl
              -> ClosureDecision.t
end = struct
  structure CF = ControlFlow
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure PackID = SharingAnalysis.PackID
  structure Prob = Probability
  structure S = SyntacticInfo
  structure SA = SharingAnalysis
  structure W = Web

  fun initial (cps: LCPS.function, syn: S.t) =
    let fun collect syn (group, (repr, allo, heap)) =
          let val functions = S.groupFun syn group
              val fv = LV.Map.listKeys (S.groupFV syn group)
              val slots = map (fn v => D.Var (v, S.typeof syn v)) fv
          in  case functions
                of #[f as (_, name, _, _, _)] =>
                     let val envid = EnvID.wrap name
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
                           Vector.foldl (fn (f as (_, name, _, _, _), (repr, heap, envs)) =>
                             let val env = EnvID.wrap name
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

         fun codePtr (D.SelectFrom { env=0, selects=[0] }, D.Boxed e, heap) =
               let val object = EnvID.Map.lookup (heap, e)
               in  case object
                     of D.Record (D.Code f :: slots) =>
                          (D.Pointer (#2 f), D.Record slots)
                      | _ => raise Fail "impossible"
               end
           | codePtr (D.SelectFrom _, _, _) = raise Fail "impossible"
           | codePtr (p as (D.Direct _ | D.Pointer _ | D.Defun _),
                      D.Boxed e, heap) = (p, EnvID.Map.lookup (heap, e))
           | codePtr _ = raise Fail "impossible"

         fun expandRepr (f, repr, heap) =
           let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
               val (code, env, heap) =
                 (case env
                    of D.Boxed e =>
                         let val (codep, obj) = codePtr (code, env, heap)
                             val heap = EnvID.Map.insert (heap, e, obj)
                         in  (codep, D.Flat [D.EnvID e, D.Null, D.Null], heap)
                         end
                     | D.Flat slots =>
                         let val length = List.length slots
                             val diff   = 3 - length
                         in  if diff > 0 then
                               (code,
                                D.Flat
                                  (slots@List.tabulate (diff, fn _ => D.Null)),
                                heap)
                             else if diff = 0 then
                               (code, env, heap)
                             else
                               raise Fail "impossible"
                         end)
                val repr =
                  LCPS.FunMap.insert (repr, f, D.Closure { code=code, env=env })
            in  (repr, heap)
           end

         val (repr, heap) = S.foldF syn (fn (f, (repr, heap)) =>
             if isEscapingCont f then
               expandRepr (f, repr, heap)
             else
               (repr, heap)
           ) (repr, heap)

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
                           List.tabulate (3, fn i => D.Expand (v, i, bogusTy))
                           @ (D.Var (v, ty) :: go xs)
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

  fun removeKnownCodePtr (web: W.t, syn: S.t) (D.T {repr, allo, heap}): D.t =
    let fun needCodePtr f =
          let val w = W.webOfFun (web, f)
          in  case W.content (web, w)
                of { polluted=false, defs=(#[_]), ... } => false
                 | _ => true
          end
        fun needCodePtr (f: LCPS.function) =
          let val name = #2 f
              fun isCall (LCPS.APP (_, CPS.VAR v, _)) = LV.same (v, name)
                | isCall _ = false
              val uses = S.usePoints syn name
          in  not (LCPS.Set.all isCall uses)
          end
        fun removeCodePtr (f, code, env, repr, heap) =
          (case (code, env)
             of (D.SelectFrom {env=0, selects=[0]}, D.Boxed e) =>
                  let val object =
                        (case EnvID.Map.lookup (heap, e)
                           of D.Record (D.Code _ :: slots) => D.Record slots
                            | _ => raise Fail "impossible")
                      val closure = D.Closure {code=D.Direct f, env=D.Boxed e}
                      val heap = EnvID.Map.insert (heap, e, object)
                      val repr = LCPS.FunMap.insert (repr, f, closure)
                  in  (repr, EnvID.Map.insert (heap, e, object))
                  end
              | (D.SelectFrom _, _) => raise Fail "impossible"
              | ((D.Pointer _ | D.Defun _), env) =>
                  let val closure = D.Closure {code=D.Direct f, env=env}
                      val repr = LCPS.FunMap.insert (repr, f, closure)
                  in  (repr, heap)
                  end
              | (D.Direct _, _) => (repr, heap))

        val (repr, heap) = LCPS.FunMap.foldli (
          fn (f, cl as D.Closure {code, env}, (repr, heap)) =>
            if not (needCodePtr f) then
              removeCodePtr (f, code, env, repr, heap)
            else
              (repr, heap)
          ) (repr, heap) repr
    in  D.T { repr=repr, heap=heap, allo=allo }
    end

  fun allocate'n'expand
    (syn: S.t, funtbl: CF.funtbl, looptbl: CF.looptbl)
    (D.T { repr, heap, allo })
  : D.t =
    let fun trueFV ([], repr, heap) = []
          | trueFV ((x as D.Var (v, ty)) :: xs, repr, heap) =
              (case S.knownFun syn v
                 of SOME f =>
                      let val D.Closure {code, env} =
                            LCPS.FunMap.lookup (repr, f)
                      in  case env
                            of D.Boxed e => x :: trueFV (xs, repr, heap)
                             | D.Flat _ => trueFV (xs, repr, heap)
                      end
                  | NONE => x :: trueFV (xs, repr, heap))
          | trueFV ((x as D.Expand (v, i, ty)) :: xs, repr, heap) =
              (case S.knownFun syn v
                 of SOME f =>
                      let val D.Closure {code, env} =
                            LCPS.FunMap.lookup (repr, f)
                      in  case env
                            of D.Boxed _ => raise Fail "expanding box"
                             | D.Flat slots =>
                                 (case List.sub (slots, i)
                                    of (D.Null | D.Code _) => trueFV (xs, repr, heap)
                                     | _ => x :: trueFV (xs, repr, heap))
                      end
                  | NONE => x :: trueFV (xs, repr, heap))
          | trueFV ((x as D.EnvID e) :: xs, repr, heap) =
              (case EnvID.Map.lookup (heap, e)
                 of D.Record [] => trueFV (xs, repr, heap)
                  | D.Record [y] => y :: trueFV (xs, repr, heap)
                  | _ => x :: trueFV (xs, repr, heap))
          | trueFV (x :: xs, repr, heap) = x :: trueFV (xs, repr, heap)

        (* fun removeConstants [] = [] *)
        (*   | removeConstants (D.Null :: xs) = removeConstants xs *)
        (*   | removeConstants (x :: xs) = x :: removeConstants xs *)

        fun lookupBlock b = CF.Graph.NodeTbl.lookup looptbl (CF.Graph.Node b)
        fun mergePref ((lvl1, prob1), (lvl2, prob2)) =
          let val lvl = Int.max (lvl1, lvl2)
              val prob = Real.max (prob1, prob2)
          in  (lvl, prob)
          end

        fun preference entry : (int * real) LV.Map.map =
          let fun getProb (NONE, n) = 1.0 / Real.fromInt n
                | getProb (SOME p, _) = Prob.toReal p
              val insert = LV.Map.insertWith mergePref
              val union = LV.Map.unionWith mergePref
              fun build (b as CF.Block { term, uses, fix, ... }, prob) =
                let val { nestingDepth, ... } = lookupBlock b
                    val augUses = foldl (fn ((grp, _), uses) =>
                        LV.Set.addList (uses,
                                        LV.Map.listKeys (S.groupFV syn grp))
                      ) uses fix
                    val pref = LV.Set.foldl (fn (v, pref) =>
                        insert (pref, v, (nestingDepth, prob))
                      ) LV.Map.empty augUses
                in  case term
                      of CF.Branch (_, _, b1, b2, p) =>
                           let val prob' = getProb (p, 2)
                               val p1 = build (b1, prob' * prob)
                               val p2 = build (b2, (1.0 - prob') * prob)
                           in  union (pref, union (p1, p2))
                           end
                       | CF.Switch blocks =>
                           let val n = List.length blocks
                           in  foldl (fn ((b, prob), pref) =>
                                 let val p = build (b, getProb (prob, n))
                                 in  union (pref, p)
                                 end
                               ) pref blocks
                           end
                       | _ => pref
                end
          in  build (entry, 1.0)
          end

        fun slotPref (slot, heap, pref) =
          (case slot
             of D.EnvID e =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record slots =>
                          foldl (fn (s, p) =>
                            mergePref (p, slotPref (s, heap, pref))
                          ) (~1, ~1.0) slots
                      | D.RawBlock (vs, _) =>
                          foldl (fn (v, p) =>
                            mergePref (p, LV.Map.lookup (pref, v))
                          ) (~1, ~1.0) vs)
              | (D.Var (v, _) | D.Expand (v, _, _)) =>
                  (LV.Map.lookup (pref, v)
                  handle e => (print (LV.lvarName v ^ "\n") ;raise e))
              | _ => (~1, ~1.0))

        fun sameProb (r1, r2) = Real.abs (r1 - r2) < 0.01

        fun take ([], n) = (List.tabulate (n, fn _ => D.Null), [])
          | take (xs, 0) = ([], xs)
          | take (x :: xs, n) =
              let val (taken, dropped) = take (xs, n - 1)
              in  (x :: taken, dropped)
              end

        fun pick (pref, heap, slots, n) : D.slot list * D.slot list =
          let val slotsWithPref =
                map (fn s => (s, slotPref (s, heap, pref))) slots
              fun gt ((v, (lvl1, prob1)), (w, (lvl2, prob2))) =
                if sameProb (prob1, prob2) then
                  lvl1 < lvl2
                else
                  prob1 < prob2
              val slots = map #1 (ListMergeSort.sort gt slotsWithPref)
          in  take (slots, n)
          end

        (* Environments now look like one of the following:
         * 1. Boxed e
         * 2. Flat [EnvID e, NULL, NULL]
         *
         * For either layout, we need to first replace the variables with their
         * expansion.
         * Then, clean up constants like NULL and known code pointers (be
         * careful of the needed code pointers).
         * Last, for flattened environments, allocate.
         * If the environment is a singleton, replace.
         *
         * CHECK: what if after replacement, some shared environments are empty
         * or singleton?
         *)
        fun collect (group, (repr, heap: D.heap, allo)) =
          let val () = print ("BEFORE " ^ String.concatWithMap "," (LV.lvarName o
              #2) (Vector.toList (S.groupFun syn group)) ^ "\n")
              val () = ClosureDecision.dumpOne (D.T {repr=repr, heap=heap,
              allo=allo}, syn, group)

              val environments = Group.Map.lookup (allo, group)
              val heap = foldl (fn (e, heap) =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record slots =>
                          let val slots = trueFV (slots, repr, heap)
                          in  EnvID.Map.insert (heap, e, D.Record slots)
                          end
                      | _ => heap)
                ) heap environments
                handle e => raise e
              (* val returnC = S.returnCont syn (S.groupExp syn group) *)
              val (repr, heap) = Vector.foldl (fn (f, (repr, heap)) =>
                  let val D.Closure {code, env} = LCPS.FunMap.lookup (repr, f)
                      val (env, heap) =
                        (case env
                           of D.Boxed e =>
                                (case EnvID.Map.lookup (heap, e)
                                   of D.Record [] => (D.Flat [], heap)
                                    (* | D.Record [D.EnvID e'] => *)
                                    (*     (D.Boxed e', heap) *)
                                    (* | D.Record [D.Code _] => *)
                                    (*     (env, heap) *)
                                    (* | D.Record [s] => *)
                                    (*     (D.Flat [s], heap) *)
                                    | _ => (env, heap))
                            | D.Flat (D.EnvID e :: nulls) =>
                                let val entry = LCPS.FunTbl.lookup funtbl f
                                    val pref = preference entry
                                    val slots =
                                      (case EnvID.Map.lookup (heap, e)
                                         of D.Record slots => slots
                                          | D.RawBlock _ =>
                                              raise Fail "impossible")
                                    val avail = List.length nulls
                                    val (taken, spilled) =
                                      pick (pref, heap, slots, avail)
                                    val heap =
                                      EnvID.Map.insert (heap, e, D.Record spilled)
                                    val fst =
                                      (case spilled
                                         of [] => D.Null
                                          | [x] => x
                                          | _ => D.EnvID e)
                                in  (D.Flat (taken @ [fst]), heap)
                                end
                            | D.Flat _ => raise Fail "impossible")
                      val closure = D.Closure {code=code, env=env}
                      val repr = LCPS.FunMap.insert (repr, f, closure)
                  in  (repr, heap)
                  end
                ) (repr, heap) (S.groupFun syn group)
                handle e => raise e
              val environments =
                List.filter (fn e =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record [] => false
                      (* | D.Record [D.Code _] => true *)
                      (* | D.Record [x] => false *)
                      | _ => true)
                ) environments
                handle e => raise e
              val allo = Group.Map.insert (allo, group, environments)

              val () = print ("AFTER " ^ String.concatWithMap "," (LV.lvarName o
              #2) (Vector.toList (S.groupFun syn group)) ^ "\n")
              val () = ClosureDecision.dumpOne (D.T {repr=repr, heap=heap,
              allo=allo}, syn, group)
          in  (repr, heap, allo)
          end
        val (repr, heap, allo) =
          Vector.foldl collect (repr, heap, allo) (S.groups syn)
    in  D.T {repr=repr, allo=allo, heap=heap}
    end

  val _ = initial : LCPS.function * S.t -> D.t
  val _ = share   : S.t * CF.block * CF.funtbl * SA.result -> rewriting
  val _ = flattenEscapingClosures : S.t * W.t -> rewriting
  val _ = segregateMLValues  : rewriting
  val _ = removeKnownCodePtr : W.t * S.t -> rewriting
  val _ = allocate'n'expand  : S.t * CF.funtbl * CF.looptbl -> rewriting

  infix 2 >>>
  fun f >>> g = fn x => g (f x)

  fun pipeline (
    cps: LCPS.function,
    syn: S.t,
    web: W.t,
    shr: SA.result,
    funtbl: CF.funtbl,
    looptbl: CF.looptbl
  ): D.t =
    let val process =
              initial
          >>> share (syn, LCPS.FunTbl.lookup funtbl cps, funtbl, shr)
          >>> removeKnownCodePtr (web, syn)
          >>> flattenEscapingClosures (syn, web)
          >>> segregateMLValues
          >>> allocate'n'expand (syn, funtbl, looptbl)

        val decision = process (cps, syn)
        val () = print "FINAL\n"
        val () = ClosureDecision.dump (decision, syn)
    in  decision
    end
end
