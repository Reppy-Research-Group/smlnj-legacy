functor ClosureDecisionPipeline(MachSpec : MACH_SPEC) :> sig
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
  structure FA = FlatteningAnalysis(MachSpec)

  val maxgpregs = MachSpec.numRegs
  val maxfpregs = MachSpec.numFloatRegs - 2  (* need 1 or 2 temps *)
  val numCSgpregs = MachSpec.numCalleeSaves
  val numCSfpregs = MachSpec.numFloatCalleeSaves
  val unboxedfloat = MachSpec.unboxedFloats
  val spillAreaSz = MachSpec.spillAreaSz

  fun isFltCty (CPS.FLTt _) = unboxedfloat
    | isFltCty _ = false

  fun numgp (m,CPS.CNTt::z) = numgp(m-numCSgpregs-1,z)
    | numgp (m,x::z) = if isFltCty(x) then numgp(m,z) else numgp(m-1,z)
    | numgp (m,[]) = m

  fun numfp (m,CPS.CNTt::z) = numfp(m-numCSfpregs,z)
    | numfp (m,x::z) = if isFltCty(x) then numfp(m-1,z) else numfp(m,z)
    | numfp (m,[]) = m

  fun argmin f [] = raise Empty
    | argmin f (x :: xs) =
        let fun go ([], arg, min) = arg
              | go (x :: xs, arg, min) =
                  let val y = f x
                  in  if y < min then go (xs, x, y) else go (xs, arg, min)
                  end
        in  go (xs, x, f x)
        end

  fun splitMin (f : 'a -> int) (xs : 'a list) : 'a * 'a list =
    let fun go (pre, _, minEl, []) = (minEl, pre)
          | go (pre, minN, minEl, x :: xs) =
             let val currN = f x
             in  if currN < minN then
                   let val (m, post) = go ([], currN, x, xs)
                   in  (m, minEl :: pre @ post)
                   end
                 else
                   go (x :: pre, minN, minEl, xs)
             end
    in  case xs
          of [] => raise Empty
           | [x] => (x, [])
           | x :: xs => go ([], f x, x, xs)
    end

  fun countif f xs =
    let fun go ([], cnt) = cnt
          | go (x :: xs, cnt) =
              if f x then go (xs, cnt + 1) else go (xs, cnt)
    in  go (xs, 0)
    end

  val _ = argmin  : ('a -> int)  -> 'a list -> 'a
  val _ = countif : ('a -> bool) -> 'a list -> int

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
                             D.Record (D.Code f :: slots, false))
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
                           EnvID.Map.insert (heap, shareEnv, D.Record (slots, true))
                         val (repr, heap, envs) =
                           Vector.foldl (fn (f as (_, name, _, _, _), (repr, heap, envs)) =>
                             let val env = EnvID.wrap name
                                 val heap =
                                   EnvID.Map.insert (heap, env,
                                     D.Record ([D.Code f, D.EnvID shareEnv], false))
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
       of D.Record (slots, shared) =>
            let fun keep (D.Var (v, _)) = LV.Set.member (vars, v)
                  | keep (D.Expand (v, _, _)) = LV.Set.member (vars, v)
                  | keep _ = true
                val slots = List.filter keep slots @ map D.EnvID packs
            in  D.Record (slots, shared)
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
          let val SA.Pack { packs, loose, ... } = Group.Tbl.lookup grpTbl grp
              val packs = PackID.Set.listItems packs
              val packEnvs = map envOfPack packs
              val heap =
                (case Group.Map.lookup (allo, grp)
                   of env :: _ =>
                        let val object = EnvID.Map.lookup (heap, env)
                            val object = replaceVars (object, loose, packEnvs)
                        in  EnvID.Map.insert (heap, env, object)
                        end
                    | _ => raise Fail "No env in a group")

              (* val replacing = foldl (fn (pack, vars) => *)
              (*     let val SA.Pack { fv, ... } = PackID.Tbl.lookup packTbl pack *)
              (*     in  LV.Set.union (vars, fv) *)
              (*     end *)
              (*   ) LV.Set.empty packs *)

              (* val heap = foldl (fn (envid, heap) => *)
              (*     let val object = EnvID.Map.lookup (heap, envid) *)
              (*         val object = replaceVars (object, replacing, packEnvs) *)
              (*     in  EnvID.Map.insert (heap, envid, object) *)
              (*     end *)
              (*   ) heap allocated *)

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
                  in  EnvID.Map.insert (heap, env, D.Record (slots, true))
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

  fun flatten (
    arity: W.id -> FA.arity,
    syn: S.t,
    web: W.t
  ) (D.T {repr, allo, heap}) =
    (* Step 1: allocate a bunch of NIL for all escaping closures' reprs. *)
     let fun needsFlatteningF f =
           let val w = W.webOfFun (web, f)
               (* val () = *)
               (*   app print [W.idToString w, " ---> ", FA.toString (arity w), "\n"] *)
           in  arity w
           end

         fun codePtr (D.SelectFrom { env=0, selects=[0] }, D.Boxed e, heap) =
               let val object = EnvID.Map.lookup (heap, e)
               in  case object
                     of D.Record (D.Code f :: slots, shared) =>
                          (D.Pointer (#2 f), D.Record (slots, shared))
                      | _ => raise Fail "impossible"
               end
           | codePtr (D.SelectFrom _, _, _) = raise Fail "impossible"
           | codePtr (p as (D.Direct _ | D.Pointer _ | D.Defun _),
                      D.Boxed e, heap) = (p, EnvID.Map.lookup (heap, e))
           | codePtr _ = raise Fail "impossible"

         fun expandRepr (f, n, repr, heap) =
           let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
               fun nuls n = List.tabulate (n, fn _ => D.Null)
               val (code, env, heap) =
                 (case env
                    of D.Boxed e =>
                         let val (codep, obj) = codePtr (code, env, heap)
                             val heap = EnvID.Map.insert (heap, e, obj)
                         in  (codep, D.Flat (D.EnvID e :: nuls (n - 1)), heap)
                         end
                     | D.Flat [] =>
                         if n = 0 then
                           (code, D.Flat [], heap)
                         else
                           raise Fail "inconsistent arity"
                     | (D.Flat _ | D.FlatAny _) => raise Fail "impossible")
                     (* | D.Flat slots => *)
                     (*     let val length = List.length slots *)
                     (*         val diff   = n - length *)
                     (*     in  if diff < 0 then *)
                     (*           raise Fail "reducing flattening" *)
                     (*         else *)
                     (*           (code, D.Flat (slots @ nuls diff), heap) *)
                     (*     end) *)
                val repr =
                  LCPS.FunMap.insert (repr, f, D.Closure { code=code, env=env })
            in  (repr, heap)
           end

         fun flexibleRepr (f, repr) =
           let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
               val env =
                 (case env
                    of D.Boxed e => D.FlatAny e
                     | D.Flat [] => D.Flat []
                     | (D.Flat _ | D.FlatAny _) => raise Fail "impossible")
               val repr =
                 LCPS.FunMap.insert (repr, f, D.Closure { code=code, env=env })
           in  repr
           end

         val (repr, heap) = S.foldF syn (fn (f, (repr, heap)) =>
             (case needsFlatteningF f
                of FA.One => (repr, heap)
                 | FA.Fixed arity =>
                     (* (app print [LV.lvarName (#2 f) , " ---> ", Int.toString arity, "\n"]; *)
                     expandRepr (f, arity, repr, heap)
                 | FA.Any _ => (flexibleRepr (f, repr), heap))
           ) (repr, heap)

         (* Step 2: replace all variables in the heap with the expansions *)
         (* Do not need to go through reprs because they don't have expansions
          * yet *)

         (* fun isContVar (v, CPS.CNTt) = true *)
         (*   | isContVar _ = false *)
         fun needCodePtr id =
           let val { defs, polluted, ... } = Web.content (web, id)
           in  if polluted then
                 true
               else
                 let val f = Vector.sub (defs, 0)
                     val D.Closure { code, ... } =
                       LCPS.FunMap.lookup (repr, f)
                 in  case code of D.Direct _ => false | _ => true
                 end
           end

         fun needsFlatteningV (v, ty) =
           (case (W.webOfVar (web, v), ty)
              of (NONE, CPS.CNTt) => (FA.Fixed 3, true)
               | (NONE, _) => (FA.One, true)
               | (SOME id, _) => (arity id, needCodePtr id))

         val bogusTy = CPSUtil.BOGt
         fun expandObject (D.Record (slots, shared)) =
               let fun go [] = []
                     | go ((x as D.Var (v, ty))::xs) =
                         (case needsFlatteningV (v, ty)
                            of (FA.One, _) => x :: go xs
                             | (FA.Fixed n, needCP) =>
                                 List.tabulate
                                   (n, fn i => D.Expand (v, i, bogusTy))
                                 @ (if needCP then (x :: go xs) else go xs)
                             | (FA.Any f, _) =>
                                 (D.ExpandAny f) :: go xs)
                     | go (x :: xs) = x :: go xs
               in  D.Record (go slots, shared)
               end
           | expandObject obj = obj
         val heap = EnvID.Map.map expandObject heap
     in  D.T { repr=repr, allo=allo, heap=heap }
     end

  fun analyze'n'flatten (syn, web) dec =
    let val arity = FA.decide (dec, web, syn)
    in  flatten (arity, syn, web) dec
    end

  fun isFloatTy (CPS.FLTt _) = true
    | isFloatTy _ = false

  fun isUntaggedIntTy (CPS.NUMt { tag, ... }) = not tag
    | isUntaggedIntTy _ = false

  fun isMLTy ty = not (isFloatTy ty) andalso not (isUntaggedIntTy ty)

  fun isMLSlot (D.Var (_, ty)) = isMLTy ty
    | isMLSlot (D.Expand (_, _, ty)) = isMLTy ty
    | isMLSlot _ = true

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
                 | D.Record (slots, shared) =>
                     let val (slots, ints, flts) = partitionSlots slots
                         val (intEnv, heap) =
                           maybeAllocRaw (ints, heap, CPS.RK_RAWBLOCK)
                         val (fltEnv, heap) =
                           maybeAllocRaw (flts, heap, CPS.RK_RAW64BLOCK)
                         val envs =
                           List.mapPartial (Option.map D.EnvID) [intEnv, fltEnv]
                         val heap =
                           EnvID.Map.insert (heap, env,
                                             D.Record (slots @ envs, shared))
                     in  (concatPartial [intEnv, fltEnv], heap)
                     end
          end
        val scanTbl = EnvID.Tbl.mkTable (32, Fail "scanTbl")
        fun scan' (env, heap): EnvID.t list * D.heap =
          (case EnvID.Tbl.find scanTbl env
             of SOME additional => (additional, heap)
              | NONE =>
                  let val (additional, heap) = scan (env, heap)
                  in  EnvID.Tbl.insert scanTbl (env, additional);
                      (additional, heap)
                  end)
        val (allo, heap) = Group.Map.foldli (fn (grp, envs, (allo, heap)) =>
            let val (envs, heap) = foldr (fn (env, (envs, heap)) =>
                    let val (additional, heap) = scan' (env, heap)
                    in  (additional @ (env :: envs), heap)
                    end
                  ) ([], heap) envs
                val allo = Group.Map.insert (allo, grp, envs)
            in  (allo, heap)
            end
          ) (allo, heap) allo
    in  D.T { repr=repr, allo=allo, heap=heap }
    end
    handle e => raise e

  fun removeKnownCodePtr (web: W.t, syn: S.t) (D.T {repr, allo, heap}): D.t =
    let
        fun inDataStructureOne name =
          let fun construct (LCPS.RECORD _) = true
                | construct (LCPS.PURE _) = true
                | construct (LCPS.SETTER _) = true
                | construct (LCPS.LOOKER _) = true
                | construct (LCPS.ARITH _) = true
                | construct _ = false
              val uses = S.usePoints syn name
          in  LCPS.Set.exists construct uses
          end
        fun inDataStructure uses = Vector.exists inDataStructureOne uses
        fun needCodePtrWeb (web, w) =
            case W.content (web, w)
              of { polluted=false, defs=(#[_]), uses=(#[v]), kind=W.Cont } =>
                   false (* Continuations do not appear in data structures *)
               | { polluted=false, defs=(#[_]), uses, kind=W.User } =>
                   inDataStructure uses
               | _ => true
        fun needCodePtr f = needCodePtrWeb (web, W.webOfFun (web, f))
        (* fun needCodePtr (f: LCPS.function) = *)
        (*   let val name = #2 f *)
        (*       fun isCall (LCPS.APP (_, CPS.VAR v, _)) = LV.same (v, name) *)
        (*         | isCall _ = false *)
        (*       val uses = S.usePoints syn name *)
        (*       val groupfuns = S.groupFun syn (S.groupOf syn f) *)
        (*   in  not (LCPS.Set.all isCall uses) *)
        (*       (1* orelse Vector.length groupfuns > 1 *1) *)
        (*   end *)
        fun removeCodePtr (f, code, env, repr, heap) =
          (case (code, env)
             of (D.SelectFrom {env=0, selects=[0]}, D.Boxed e) =>
                  let val object =
                        (case EnvID.Map.lookup (heap, e)
                           of D.Record (D.Code _ :: slots, shared) =>
                                D.Record (slots, shared)
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

  fun removeEmptyEnv (syn: S.t, web: W.t) (D.T {repr, heap, allo}) : D.t =
    let fun collect (id, { defs, uses, polluted, ... }: W.info, arity0webs) =
          let fun isArity0V v =
                (case W.webOfVar (web, v)
                   of NONE => false
                    | SOME id => W.Set.member (arity0webs, id))
              fun isArity0S (D.EnvID e) =
                    (case EnvID.Map.lookup (heap, e)
                       of D.Record (slots, _) => List.all isArity0S slots
                        | D.RawBlock ([_], _) => raise Fail "empty raw"
                        | D.RawBlock _ => false)
                | isArity0S (D.Var (v, _)) = isArity0V v
                | isArity0S (D.Expand (v, _, _)) = isArity0V v
                | isArity0S (D.ExpandAny _) = raise Fail "unexpected expand any"
                | isArity0S (D.Code _) = false
                | isArity0S D.Null = raise Fail "unexpected null"
              fun isArity0F f =
                let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
                in  case (code, env)
                      of (_, D.Boxed e) => isArity0S (D.EnvID e)
                       | (D.Direct _, D.Flat []) => true
                       | _ => false
                end
          in  if polluted then
                arity0webs
              else if Vector.all isArity0F defs then
                W.Set.add (arity0webs, id)
              else
                arity0webs
          end
        fun fixpt (n, arity0webs) =
          let val arity0webs' = W.fold collect arity0webs web
          in  if W.Set.equal (arity0webs, arity0webs') then
                arity0webs'
              else
                fixpt (n + 1, arity0webs')
          end
        val arity0webs = fixpt (0, W.Set.empty)
        (* val () = app print [ *)
        (*     "arity0webs: ", String.concatWithMap "," W.idToString *)
        (*     (W.Set.listItems arity0webs), *)
        (*     "\n" *)
        (*   ] *)

        fun purge (grp, (repr, heap, allo)) =
          let val functions = S.groupFun syn grp
              fun purgeSlots ([], heap) = []
                | purgeSlots ((x as (D.Var (v, _) | D.Expand (v, _, _))) :: xs,
                              heap) =
                    (case W.webOfVar (web, v)
                       of NONE => x :: purgeSlots (xs, heap)
                        | SOME id =>
                            if W.Set.member (arity0webs, id) then
                              purgeSlots (xs, heap)
                            else
                              x :: purgeSlots (xs, heap))
                | purgeSlots ((D.ExpandAny _) :: xs, _) =
                    raise Fail "impossible"
                | purgeSlots ((x as D.EnvID e) :: xs, heap) =
                    (case EnvID.Map.lookup (heap, e)
                       of D.Record ([], _) => purgeSlots (xs, heap)
                        | _ => x :: purgeSlots (xs, heap))
                | purgeSlots (x :: xs, heap) = x :: purgeSlots (xs, heap)
              val environments = Group.Map.lookup (allo, grp)
              val heap = foldl (fn (e, heap) =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record (slots, shr) =>
                          let val slots = purgeSlots (slots, heap)
                          in  EnvID.Map.insert (heap, e, D.Record (slots, shr))
                          end
                      | _ => heap)
                ) heap environments
              val repr = Vector.foldl (fn (f, repr) =>
                  let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
                      val env =
                        (case env
                           of D.Boxed e =>
                                (case EnvID.Map.lookup (heap, e)
                                   of D.Record ([], _) => D.Flat []
                                    (* | D.Record ([D.EnvID e'], _) => D.Boxed e' *)
                                    | _ => env)
                            | D.FlatAny _ => raise Fail "impossible"
                            | D.Flat slots =>
                                D.Flat (purgeSlots (slots, heap)))
                      val closure =D.Closure { code=code, env=env }
                  in  LCPS.FunMap.insert (repr, f, closure)
                  end
                ) repr functions
              val environments =
                List.filter (fn e =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record ([], _) => false
                      (* | D.Record ([D.EnvID _], _) => false *)
                      | _ => true)
                ) environments
              val allo = Group.Map.insert (allo, grp, environments)
          in  (repr, heap, allo)
          end
        val (repr, heap, allo) =
          Vector.foldl purge (repr, heap, allo) (S.groups syn)
    in  D.T {repr=repr, allo=allo, heap=heap}
    end

  fun removeSingletonEnv (D.T { repr, heap, allo }) : D.t =
    (* 1. Figure out all singleton envs
     * 2. Figure out all necessary single envs ( Boxed )
     * 3. Remove from alloc and remove from each env *)
    let type repl = D.slot EnvID.Map.map
        fun collectSingleton (id, obj, singletons: repl) =
          (case obj
             of D.Record ([x], _) =>
                  EnvID.Map.insert (singletons, id, x)
              | _ => singletons)
        val replacement =
          EnvID.Map.foldli collectSingleton EnvID.Map.empty heap
        (* fun compress (x as D.EnvID e) = *)
        (*       (case EnvID.Map.find (replacement, e) *)
        (*          of SOME slot => compress slot *)
        (*           | NONE => x) *)
        (*   | compress x = x *)
        (* val replacement = EnvID.Map.map compress replacement *)
        fun findChain (map: repl, e) =
          (case EnvID.Map.find (map, e)
             of SOME (D.EnvID e') => findChain (map, e')
              | (NONE | SOME _) => e)
        fun remove (map, e) =
          (case EnvID.Map.findAndRemove (map, e)
             of SOME (map', _) => map'
              | NONE => map)
        fun clearNecessary (_, D.Closure { env, code }, singletons: repl) =
          (case env
             of D.Boxed e =>
                  let val e' = findChain (singletons, e)
                  in  if EnvID.same (e, e') then
                        remove (singletons, e)
                      else
                        remove (
                          EnvID.Map.insert (singletons, e, D.EnvID e'),
                          e'
                        )
                  end
              | _ => singletons)
        val replacement = LCPS.FunMap.foldli clearNecessary replacement repr

        val () = EnvID.Map.appi
          (fn (e, s) => print (
            "Removing: " ^ EnvID.toString e ^ " --> " ^ D.slotToString s ^ "\n"))
          replacement

        fun replace (x as D.EnvID e) =
              (case EnvID.Map.find (replacement, e)
                 of SOME slot => replace slot
                  | NONE => x)
          | replace x = x

        fun removeAlloc allocs =
          List.filter (fn e => not (EnvID.Map.inDomain (replacement, e))) allocs
        fun replaceObj (e, obj) =
          (case EnvID.Map.find (replacement, e)
             of NONE =>
                  (case obj
                     of D.Record (slots, shared) =>
                          SOME (D.Record (map replace slots, shared))
                      | _ => SOME obj)
              | SOME _ => NONE)
        fun replaceRepr (clo as D.Closure { code, env }) =
          (case env
             of D.Boxed e =>
                  (case replace (D.EnvID e)
                     of (D.EnvID e') =>
                          D.Closure { code=code, env=D.Boxed e' }
                      | _ => raise Fail "boxed becomes unboxed")
              | D.FlatAny slots => raise Fail "unresolved flat any"
              | D.Flat slots =>
                  D.Closure { code=code, env=D.Flat (map replace slots) })
        val allo = Group.Map.map removeAlloc allo
        val heap = EnvID.Map.mapPartiali replaceObj heap
        val repr = LCPS.FunMap.map replaceRepr repr
    in  D.T { allo=allo, heap=heap, repr=repr }
    end
    handle e => raise e

  fun unshare
    (syn: S.t, funtbl: CF.funtbl, looptbl: CF.looptbl)
    (D.T { allo, heap, repr })
  : D.t =
    (* FIXME: If the function is free in a later function, do not unshare *)
    let fun innerFs (CF.Block { term, fix, ... }) =
          (case term
             of CF.Branch (_, _, b1, b2, _) =>
                  fix @ innerFs b1 @ innerFs b2
              | CF.Switch blocks =>
                  foldl (fn ((b, _), fix) => innerFs b @ fix) fix blocks
              | _ => fix)
        fun searchEnvs (heap, grp, fs, set: EnvID.Set.set) =
          let fun searchSlots ([], set) = set
                | searchSlots (D.EnvID e :: todo, set) =
                    if EnvID.Set.member (set, e) then
                      searchSlots (todo, set)
                    else
                      (case EnvID.Map.lookup (heap, e)
                         of D.Record (slots, _) =>
                              searchSlots (slots @ todo, EnvID.Set.add (set, e))
                          | D.RawBlock _ => searchSlots (todo, set))
                | searchSlots (_ :: todo, set) = searchSlots (todo, set)
              val environments = Group.Map.lookup (allo, grp)
              val set =
                foldl (fn (e, set) => searchSlots ([D.EnvID e], set)) set
                      environments
              val set =
                foldl (fn (f, set) =>
                  let val D.Closure { env, ... } = LCPS.FunMap.lookup (repr, f)
                  in  case env
                        of D.Flat slots => searchSlots (slots, set)
                         | D.FlatAny _ => raise Fail "unexpected flat any"
                         | D.Boxed e => searchSlots ([D.EnvID e], set)
                  end
                ) set fs
          in  set
          end
        fun freeInInners (f: LCPS.function, fixes: CF.fix list) =
          let fun freeIn (grp, _) =
                let val fv = S.groupFV syn grp
                in  LV.Map.inDomain (fv, #2 f)
                end
          in  List.exists freeIn fixes
          end
        fun getUsage (heap: D.heap) =
          let fun usedBy (census, f, env) =
                (case LCPS.FunMap.find (census, f)
                   of NONE => LCPS.FunMap.insert (census, f, [env])
                    | SOME envs => LCPS.FunMap.insert (census, f, env :: envs))
              fun scan env (D.Var (v, _), census) =
                    (case S.knownFun syn v
                       of NONE => census
                        | SOME f => usedBy (census, f, env))
                | scan env (D.Expand _, census) =
                    raise Fail "expand before flatten"
                | scan env (_, census) = census
              fun collect (env, object, census: EnvID.t list LCPS.FunMap.map) =
                (case object
                   of D.Record (slots, _) => foldl (scan env) census slots
                    | D.RawBlock _ => census)
          in  EnvID.Map.foldli collect LCPS.FunMap.empty heap
          end
        val usage = getUsage heap
        fun numUsage f =
          (case LCPS.FunMap.find (usage, f)
             of NONE => 0
              | SOME envs => List.length envs)
        fun flattenUnneeded (heap, f, inners) =
          let val dependents =
                foldl (fn ((grp, fs), set) =>
                  searchEnvs (heap, grp, fs, set)
                ) EnvID.Set.empty inners
              val (e, slots) =
                (case LCPS.FunMap.lookup (repr, f)
                   of D.Closure { env=D.Boxed e, ... } =>
                        (case EnvID.Map.lookup (heap, e)
                           of D.Record (slots, false) => (e, slots)
                            | D.Record (_, true) =>
                                raise Fail "impossible"
                            | D.RawBlock _ =>
                                raise Fail "impossible")
                    | _ => raise Fail "impossible")
              val slots =
                foldr
                  (fn (D.EnvID e', slots) =>
                      if not (EnvID.Set.member (dependents, e')) then
                        (* (print ("HIT: " ^ EnvID.toString e' ^ "\n"); *)
                        (case EnvID.Map.lookup (heap, e')
                           of D.Record (slots', false) =>
                                raise Fail "nested unshared records"
                            | D.Record (slots', true) =>
                                slots' @ slots
                            | D.RawBlock _ =>
                                raise Fail "RawBlock")
                        (* ) *)
                      else
                        (D.EnvID e' :: slots)
                    | (x, slots) => x :: slots) [] slots
              val heap =
                EnvID.Map.insert (heap, e, D.Record (slots, false))
          in  heap
          end
        fun processGrp (grp, heap) (* : D.heap * EnvID.Set.set *) =
          (case S.groupFun syn grp
             of #[f as (CPS.KNOWN_TAIL, name, _, _, _)] =>
                  let val inners = innerFs (LCPS.FunTbl.lookup funtbl f)
                  in  if freeInInners (f, inners) orelse numUsage f >= 2 then
                        heap
                      else
                        flattenUnneeded (heap, f, inners)
                  end
              | _ => heap)
        val heap = Vector.foldr processGrp heap (S.groups syn)
    in  D.T { allo=allo, heap=heap, repr=repr }
    end

  fun mergePref ((lvl1, prob1: real), (lvl2, prob2: real)) =
    let val lvl = Int.max (lvl1, lvl2)
        (* val lvl = lvl1 + lvl2 *)
        val prob = prob1 + prob2
    in  (lvl, prob)
    end

  fun getPreference (
    looptbl: CF.looptbl,
    funtbl: CF.funtbl,
    syn: S.t,
    f: LCPS.function
  ) : (int * real) LV.Map.map =
    let fun lookupBlock b = CF.Graph.NodeTbl.lookup looptbl (CF.Graph.Node b)
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
    in  preference (LCPS.FunTbl.lookup funtbl f)
    end

  fun pickNSlots (pref, heap, slots, n) : D.slot list * D.slot list =
    let val botPref = (~1, ~1.0)
        fun slotPref (slot, heap, pref) =
          (case slot
             of D.EnvID e =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record (slots, _) =>
                          foldl (fn (s, p) =>
                            mergePref (p, slotPref (s, heap, pref))
                          ) botPref slots
                      | D.RawBlock (vs, _) =>
                          foldl (fn (v, p) =>
                            (case LV.Map.find (pref, v)
                               of SOME p' => mergePref (p, p')
                                | NONE => p)
                          ) botPref vs)
              | (D.Var (v, _) | D.Expand (v, _, _)) =>
                  (* This is possible because a closure may close over a known
                   * function, and it is save to share everything in that
                   * function's closure even though some variables may not be
                   * used directly *)
                  (case LV.Map.find (pref, v)
                     of NONE => botPref
                      | SOME p => p)
              | _ => botPref)

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
              (* fun gt ((v, (lvl1, prob1)), (w, (lvl2, prob2))) = *)
              (*   if lvl1 = lvl2 then *)
              (*     prob1 < prob2 *)
              (*   else *)
              (*     lvl1 < lvl2 *)
              (* TODO: Measure use counts *)
              val slots = ListMergeSort.sort gt slotsWithPref
              (* val () = ( *)
              (*   print "PRIORITY: "; *)
              (*   print (String.concatWithMap "," (fn (s, (lvl, prob)) => *)
              (*     concat ["(", D.slotToString s, ",", Int.toString lvl, ",", *)
              (*             Real.toString prob, ")"]) slots); *)
              (*   print "\n" *)
              (* ) *)
              val slots = map #1 slots
          in  take (slots, n)
          end
    in  pick (pref, heap, slots, n)
    end

  fun allocate'n'expand
    (syn: S.t, web: W.t, funtbl: CF.funtbl, looptbl: CF.looptbl)
    (D.T { repr, heap, allo })
  : D.t =
    let
        (* fun needCodePtr v = *)
        (*   (case W.webOfVar (web, v) *)
        (*      of SOME w => needCodePtrWeb (web, w) *)
        (*       | NONE => true) *)
        fun markEnv (heap, e, shared) =
          (case EnvID.Map.lookup (heap, e)
             of D.Record (slots, _) =>
                  EnvID.Map.insert (heap, e, D.Record (slots, shared))
              | _ => heap)
        fun markShared (heap, e) = markEnv (heap, e, true)
        fun trueFV ([], repr, heap) = ([], heap)
          | trueFV ((x as D.Var (v, ty)) :: xs, repr, heap) =
              (case S.knownFun syn v
                 of SOME f =>
                      let val D.Closure {code, env} =
                            LCPS.FunMap.lookup (repr, f)
                          val (xs, heap) = trueFV (xs, repr, heap)
                      in  case env
                            of D.Boxed e =>
                                 (D.EnvID e :: xs, markShared (heap, e))
                             | D.FlatAny _ => raise Fail "unimp"
                             | D.Flat _ => (xs, heap)
                      end
                  | NONE =>
                      let val (xs, heap) = trueFV (xs, repr, heap)
                      in  (x :: xs, heap)
                      end)
          | trueFV ((x as D.Expand (v, i, ty)) :: xs, repr, heap) =
              (case S.knownFun syn v
                 of SOME f =>
                      (let val D.Closure {code, env} =
                            LCPS.FunMap.lookup (repr, f)
                          val (xs, heap) = trueFV (xs, repr, heap)
                      in  case env
                            of D.Boxed _ => raise Fail "expanding box"
                             | D.FlatAny _ =>
                                 raise Fail "Expand on flat any"
                             | D.Flat [] => (xs, heap)
                             | D.Flat slots =>
                                 (case List.sub (slots, i)
                                    of (D.Null | D.Code _) => (xs, heap)
                                     | x as D.EnvID e =>
                                         (x :: xs, markShared (heap, e))
                                     | x => (x :: xs, heap))
                      end
                      handle e =>
                      (print (LV.lvarName (#2 f) ^ "!\n");
                       D.dump (D.T {repr=repr, heap=heap, allo=allo}, syn);
                       raise e))
                  | NONE =>
                      let val (xs, heap) = trueFV (xs, repr, heap)
                      in  (x :: xs, heap)
                      end)
          | trueFV ((x as D.ExpandAny f) :: xs, repr, heap) =
              let val D.Closure { code, env } = LCPS.FunMap.lookup (repr, f)
                  val (xs, heap) = trueFV (xs, repr, heap)
              in  case env
                    of D.FlatAny _ => raise Fail "unresolved flat any"
                     | D.Boxed _ => raise Fail "expanding box"
                     | D.Flat slots =>
                         let fun notConst (D.Null | D.Code _) = false
                               | notConst _ = true
                             val slots = List.filter notConst slots
                         in  (slots @ xs, heap)
                         end
              end
          | trueFV ((x as D.EnvID e) :: xs, repr, heap) =
              let val (xs, heap) = trueFV (xs, repr, heap)
              in  case EnvID.Map.lookup (heap, e)
                    of D.Record ([], _) => (xs, heap)
                     (* | D.Record ([y as D.EnvID e'], shared) => *)
                     (*     (y :: xs, markEnv (heap, e', shared)) *)
                     | _ => (x :: xs, heap)
              end
          | trueFV (x :: xs, repr, heap) =
              let val (xs, heap) = trueFV (xs, repr, heap)
              in  (x :: xs, heap)
              end

        val removeDup = D.SlotSet.toList o D.SlotSet.fromList

        (* fun removeConstants [] = [] *)
        (*   | removeConstants (D.Null :: xs) = removeConstants xs *)
        (*   | removeConstants (x :: xs) = x :: removeConstants xs *)
        fun isShared e =
          (case EnvID.Map.lookup (heap, e)
             of D.Record (_, shared) => shared
              | D.RawBlock _ => raise Fail "unexpected raw block")

        fun isFirstOrder (f: LCPS.function) =
          let val name = #2 f
              fun isCall (LCPS.APP (_, CPS.VAR v, _)) = LV.same (v, name)
                | isCall _ = false
              val uses = S.usePoints syn name
          in  LCPS.Set.all isCall uses
          end

        fun parentOf grp = S.enclosing syn (S.groupExp syn grp)

        fun fillbase (repr, heap, allo, pref, f, slots) =
          let fun envsInScope (CF.Block { term, fix, ... }) =
                let val envs = List.foldl (fn ((grp, _), envs) =>
                      EnvID.Set.addList (envs, Group.Map.lookup (allo, grp))
                    ) EnvID.Set.empty fix
                in  case term
                      of CF.Branch (_, _, b1, b2, _) =>
                           EnvID.Set.union (envs,
                             EnvID.Set.union (envsInScope b1, envsInScope b2))
                       | CF.Switch blocks =>
                           List.foldl (fn ((b, _), envs) =>
                             EnvID.Set.union (envs, envsInScope b)
                           ) envs blocks
                       | _ => envs
                end
              fun isInScope (parent, envsInScope) =
                let val slots =
                      (case LCPS.FunMap.lookup (repr, parent)
                         of D.Closure { env=D.Boxed e, ... } =>
                              D.SlotSet.singleton (D.EnvID e)
                          | D.Closure { env=D.FlatAny _, ... } =>
                              raise Fail "unresolved flat any"
                          | D.Closure { env=D.Flat slots, ... } =>
                              D.SlotSet.fromList slots)
                    val slots =
                      EnvID.Set.foldl (fn (e, slots) =>
                        D.SlotSet.add (slots, D.EnvID e)
                      ) slots envsInScope
                    fun islocal v =
                      let val defsite = S.defSite syn v
                      in  LV.same (#2 defsite, #2 parent)
                      end
                in  fn slot =>
                      D.SlotSet.member (slots, slot) orelse
                        (case slot
                           of (D.Var (v, _) | D.Expand (v, _, _)) => islocal v
                            | _ => false)
                end
              fun filterInScope slots =
                (case S.binderOf syn f
                   of NONE => D.SlotSet.empty
                    | SOME parent =>
                        let val envs =
                              envsInScope (LCPS.FunTbl.lookup funtbl parent)
                        in  D.SlotSet.filter (isInScope (parent, envs)) slots
                        end)
              fun fillbase' (slots, n, pref) =
                let val slots = D.SlotSet.toList (filterInScope slots)
                    (* val () = print ("Picking base for " ^ LV.lvarName (#2 f) ^ *)
                    (* "\n") *)
                    val (taken, _) = pickNSlots (pref, heap, slots, n)
                in  taken
                end

              fun scan ([], nNuls, envs, slots) = (nNuls, envs, rev slots)
                | scan (D.Null :: xs, nNuls, envs, slots) =
                    scan (xs, nNuls + 1, envs, slots)
                | scan ((s as D.EnvID e) :: xs, nNuls, envs, slots) =
                    scan (xs, nNuls, e :: envs, s :: slots)
                | scan (s :: xs, nNuls, envs, slots) =
                    scan (xs, nNuls, envs, s :: slots)
          in  case scan (slots, 0, [], [])
                of ((0, _, _) | (_, [], _)) => slots
                 | (n, envs, slots) =>
                     let val indirects = foldr (fn (e, indirects) =>
                           (case EnvID.Map.lookup (heap, e)
                              of D.Record (slots, _) =>
                                   D.SlotSet.addList (indirects, slots)
                               | D.RawBlock _ => indirects)
                         ) D.SlotSet.empty envs
                         val taken =
                           fillbase' (indirects, n, pref)
                     in  slots @ taken
                     end
          end

        fun allocate (heap, f, e, avail, availEnvs) : D.environment * D.heap =
          let val pref = getPreference (looptbl, funtbl, syn, f)
              val slots = (case EnvID.Map.lookup (heap, e)
                             of D.Record (slots, false) => slots
                              | D.Record (slots, true) =>
                                  raise Fail "destroying shared envs"
                              | D.RawBlock _ =>
                                  raise Fail "impossible")
              val (taken, spilled) =
                let val (slots, spilled) =
                      if isFirstOrder f then
                        (slots, [])
                      else
                        List.partition isMLSlot slots
                    val (taken, spilled') =
                      pickNSlots (pref, heap, slots, avail)
                in  (taken, spilled @ spilled')
                end
              fun insert (heap, e, slots) =
                EnvID.Map.insert (heap, e, D.Record (slots, false))
              (* serendipitous sharing *)
              fun update (heap, e, slots) =
                let val set = D.SlotSet.fromList slots
                    fun search [] =
                          (D.EnvID e, insert (heap, e, slots))
                      | search ((e', slots') :: avails) =
                          if D.SlotSet.equal (set, slots') then
                            (D.EnvID e', markShared (insert (heap, e, []), e'))
                          else
                            search avails
                in  search availEnvs
                end
              val (fst, heap) =
                (case spilled
                   of [] => (D.Null, insert (heap, e, []))
                    | [x] =>
                        if isMLSlot x then
                          (x, insert (heap, e, []))
                        else
                          update (heap, e, [x])
                    | _ =>
                        update (heap, e, spilled))
              val slots = taken @ [fst]
              (* val slots = fillbase (repr, heap, allo, pref, f, slots) *)
          in  (D.Flat slots, heap)
          end
        fun unbox (heap, f, e, availEnvs) : D.environment * D.heap =
          let val slots =
                (case EnvID.Map.lookup (heap, e)
                   of D.Record (slots, false) => slots
                    | D.Record (slots, true) =>
                        raise Fail "destroying shared envs"
                    | D.RawBlock _ =>
                        raise Fail "impossible")
              val () =
                if List.exists (fn (D.Code _) => true | _ => false) slots then
                  raise Fail "unboxing non direct function"
                else
                  ()
              (* val avail = numgp(maxgpregs, #4 f) *)
              (* val e1 = allocate (heap, f, e, avail, availEnvs) *)
              (* val heap = EnvID.Map.insert (heap, e, D.Record ([], false)) *)
              (* val e2 = (D.Flat slots, heap) *)
              val numArgCutOff = maxgpregs + maxfpregs
              val nargs = List.length (#3 f)
          in  if List.length slots + nargs <= numArgCutOff then
                let val heap = EnvID.Map.insert (heap, e, D.Record ([], false))
                in  (D.Flat slots, heap)
                end
              else
                allocate (heap, f, e, numArgCutOff - nargs, availEnvs)
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
          let
              (* val () = print ("BEFORE " ^ String.concatWithMap "," (LV.lvarName o *)
              (* #2) (Vector.toList (S.groupFun syn group)) ^ "\n") *)
              (* val () = ClosureDecision.dumpOne (D.T {repr=repr, heap=heap, *)
              (* allo=allo}, syn, group) *)

              val parentEnvs =
                let val parent = parentOf group
                    fun collectEnvs (D.EnvID e, lst) =
                          (case EnvID.Map.lookup (heap, e)
                             of D.Record (slots, _) =>
                                  (e, D.SlotSet.fromList slots) :: lst
                              | D.RawBlock _ => lst)
                      | collectEnvs (_, lst) = lst
                in  case LCPS.FunMap.find (repr, parent)
                      of SOME (D.Closure { env=D.Flat slots, ... }) =>
                           foldl collectEnvs [] slots
                       | _ => []
                end
              val environments = Group.Map.lookup (allo, group)
              val heap = foldl (fn (e, heap) =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record (slots, shr) =>
                          let val (slots, heap) = trueFV (slots, repr, heap)
                              val slots = removeDup slots
                          in  EnvID.Map.insert (heap, e, D.Record (slots, shr))
                          end
                      | _ => heap)
                ) heap environments
                handle e => raise e
              val (repr, heap) = Vector.foldl (fn (f, (repr, heap)) =>
                  let val D.Closure {code, env} = LCPS.FunMap.lookup (repr, f)
                      val (env, heap) =
                        (case env
                           of D.Boxed e =>
                                (case EnvID.Map.lookup (heap, e)
                                   of D.Record ([], _) =>
                                        raise Fail "empty"
                                    | _ => (env, heap)
                                handle e => raise e)
                            | D.FlatAny e =>
                                if isShared e then
                                  (D.Flat [D.EnvID e], heap)
                                else
                                  unbox (heap, f, e, parentEnvs)
                            | D.Flat [] => (D.Flat [], heap)
                            | D.Flat (D.EnvID e :: nulls) =>
                                if isShared e then
                                  (env, heap)
                                else
                                  allocate (heap, f, e, List.length nulls, parentEnvs)
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
                     of D.Record ([], _) => false
                      (* | D.Record ([D.EnvID _], _) => false *)
                      | _ => true)
                ) environments
                handle e => raise e
              val allo = Group.Map.insert (allo, group, environments)

              (* val () = print ("AFTER " ^ String.concatWithMap "," (LV.lvarName o *)
              (* #2) (Vector.toList (S.groupFun syn group)) ^ "\n") *)
              (* val () = ClosureDecision.dumpOne (D.T {repr=repr, heap=heap, *)
              (* allo=allo}, syn, group) *)
          in  (repr, heap, allo)
          end
        val (repr, heap, allo) =
          Vector.foldl collect (repr, heap, allo) (S.groups syn)
    in  D.T {repr=repr, allo=allo, heap=heap}
    end
    handle e => (D.dump (D.T {repr=repr, allo=allo, heap=heap}, syn); raise e)

  fun fixOvershare (syn, funtbl, looptbl) (D.T {repr, allo, heap}) =
    let fun scanSharedEnvAndSlack ([], sharedenvs, slack)  = (sharedenvs, slack)
          | scanSharedEnvAndSlack (D.Null :: slots, sharedenvs, slack) =
              scanSharedEnvAndSlack (slots, sharedenvs, slack + 1)
          | scanSharedEnvAndSlack (D.EnvID e :: slots, sharedenvs, slack) =
              (case EnvID.Map.lookup (heap, e) handle e => raise e
                 of D.Record (_, true) =>
                      scanSharedEnvAndSlack (slots, e :: sharedenvs, slack)
                  | _ =>
                      scanSharedEnvAndSlack (slots, sharedenvs, slack))
          | scanSharedEnvAndSlack (_ :: slots, sharedenvs, slack) =
              scanSharedEnvAndSlack (slots, sharedenvs, slack)
        datatype slack_data = NoSlack
                            | Slack of int * LCPS.function list
        fun mergeSlackData (NoSlack, _) = NoSlack
          | mergeSlackData (_, NoSlack) = NoSlack
          | mergeSlackData (Slack (slack1, fs1), Slack (slack2, fs2)) =
              Slack (Int.min (slack1, slack2), fs1 @ fs2)
        fun slackDataToString NoSlack = "No"
          | slackDataToString (Slack (slack, fs)) =
              concat [Int.toString slack, " [", String.concatWithMap ","
                      (LV.lvarName o #2) fs, "]"]
        fun recordSlack (slack, env, s, f) =
          let val insert = EnvID.Map.insertWith mergeSlackData
          in  if s = 0 then
                insert (slack, env, NoSlack)
              else
                insert (slack, env, Slack (s, [f]))
          end
        fun bestFit envs =
          let fun sz e =
                (case EnvID.Map.lookup (heap, e) handle e => raise e
                   of D.Record (slots, true) => countif isMLSlot slots
                    | _ => raise Fail "impossible")
          in  splitMin sz envs
          end
        fun collectSlack (f, D.Closure {env, code}, slack) =
          (case env
             of D.Flat slots =>
                  (case scanSharedEnvAndSlack (slots, [], 0)
                     of ([], _) => slack
                      | ([e], n) => recordSlack (slack, e, n, f)
                      | (envs, n) =>
                          let val (picked, others) = bestFit envs
                          in  foldl (fn (e, slack) =>
                                      recordSlack (slack, e, 0, f))
                                    (recordSlack (slack, picked, n, f))
                                    others
                          end)
              | D.FlatAny _ => raise Fail "unresolved flat any"
              | D.Boxed env => recordSlack (slack, env, 0, f))
        val slackmap = LCPS.FunMap.foldli collectSlack EnvID.Map.empty repr
        (* val () = *)
        (*   EnvID.Map.appi (fn (e, s) => *)
        (*     app print [EnvID.toString e, " --> ", slackDataToString s, "\n"] *)
        (*   ) slackmap *)
        val slackmap =
          EnvID.Map.mapPartial (fn NoSlack => NONE | Slack data => SOME data)
                               slackmap
        fun recordUse (usecnt, env', env) =
          if not (EnvID.Map.inDomain (slackmap, env)) then
            usecnt
          else
            EnvID.Map.insertWith (op@) (usecnt, env, [env'])
        fun useCount (envid, D.Record (slots, _), usecnt) =
              foldl (fn (D.EnvID e, usecnt) => recordUse (usecnt, envid, e)
                      | (_, usecnt) => usecnt) usecnt slots
          | useCount (_, _, usecnt) = usecnt
        val usecnt = EnvID.Map.foldli useCount EnvID.Map.empty heap
        (* val () = *)
        (*   EnvID.Map.appi (fn (e, es) => *)
        (*     app print [EnvID.toString e, " by ", *)
        (*                String.concatWithMap "," EnvID.toString es, "\n"] *)
        (*   ) usecnt *)
        fun allocateSlack (env, (amount, functions), allocation) =
          if EnvID.Map.inDomain (usecnt, env) then
            allocation
          else
            let val pref = foldl (fn (f, pref) =>
                    let val p = getPreference (looptbl, funtbl, syn, f)
                    in  LV.Map.unionWith mergePref (pref, p)
                    end
                  ) LV.Map.empty functions
                val slots =
                  (case EnvID.Map.lookup (heap, env) handle e => raise e
                     of D.Record (slots, true) => slots
                      | _ => raise Fail "unexpected")
                val (slots, mustRemain) = List.partition isMLSlot slots
                val (taken, remains) = pickNSlots (pref, heap, slots, amount)
                val remains = remains @ mustRemain
            in  EnvID.Map.insert (allocation, env, (remains, taken))
            end
        val allocation = EnvID.Map.foldli allocateSlack EnvID.Map.empty slackmap
        (* val () = *)
        (*   EnvID.Map.appi (fn (e, (remains, taken)) => *)
        (*     app print [EnvID.toString e, " new ", *)
        (*                String.concatWithMap "," D.slotToString remains, " / ", *)
        (*                String.concatWithMap "," D.slotToString taken, "\n"] *)
        (*   ) allocation *)
        fun fillslots ([], [], _) = []
          | fillslots ([], _, _) = raise Fail "not enough NULL slots"
          | fillslots (D.Null :: slots, s :: taken, remove) =
              s :: fillslots (slots, taken, remove)
          | fillslots ((s as D.EnvID e) :: slots, taken, SOME e') =
              if EnvID.same (e, e') then
                fillslots (D.Null :: slots, taken, SOME e')
              else
                s :: fillslots (slots, taken, SOME e')
          | fillslots (s :: slots, taken, remove) =
              s :: fillslots (slots, taken, remove)
        fun updateRepr (env, (remains, taken), (repr, heap, purge)) =
          let val (amount, functions) = EnvID.Map.lookup (slackmap, env) handle e => raise e
              val (heap, remove, purge) =
                if List.null remains then
                  (#1 (EnvID.Map.remove (heap, env)),
                   SOME env,
                   EnvID.Set.add (purge, env))
                else
                  (EnvID.Map.insert (heap, env, D.Record (remains, true)),
                   NONE,
                   purge)
              val repr = foldl (fn (f, repr) =>
                  (case LCPS.FunMap.lookup (repr, f) handle e => raise e
                     of D.Closure { env=D.Flat slots, code } =>
                          let val clos = D.Closure {
                                  env=D.Flat (fillslots (slots, taken, remove)),
                                  code=code
                                }
                          in  LCPS.FunMap.insert (repr, f, clos)
                          end
                      | _ => raise Fail "expanding shared env used in non-flat")
                ) repr functions
          in  (repr, heap, purge)
          end
        val (repr, heap, purge) =
          EnvID.Map.foldli updateRepr (repr, heap, EnvID.Set.empty) allocation
        (* val () = (print "Purge:\n"; EnvID.Set.app (fn e => *)
        (*     print (EnvID.toString e ^ "\n") *)
        (*   ) purge) *)
        val allo = Group.Map.map (fn envs =>
            List.filter (fn e => not (EnvID.Set.member (purge, e))) envs
          ) allo
    in  D.T {repr=repr, allo=allo, heap=heap}
    end
    handle e => raise e

  val _ = initial : LCPS.function * S.t -> D.t
  val _ = share   : S.t * CF.block * CF.funtbl * SA.result -> rewriting
  val _ = unshare   : S.t * CF.funtbl * CF.looptbl -> rewriting
  val _ = analyze'n'flatten : S.t * W.t -> rewriting
  val _ = segregateMLValues  : rewriting
  val _ = removeKnownCodePtr : W.t * S.t -> rewriting
  val _ = removeEmptyEnv : S.t * W.t -> rewriting
  val _ = removeSingletonEnv : rewriting
  val _ = allocate'n'expand  : S.t * W.t * CF.funtbl * CF.looptbl -> rewriting

  fun fake syn (f : rewriting) : rewriting = fn dec =>
    let val () = print "BEFORE\n:"
        val () = D.dump (dec, syn)
        val dec' = f dec
        val () = print "AFTER\n:"
        val () = D.dump (dec', syn)
    in  dec
    end
  fun trace syn (f : rewriting) : rewriting = fn dec =>
    let val () = print "BEFORE\n:"
        val () = D.dump (dec, syn)
        val dec = f dec
        val () = print "AFTER\n:"
        val () = D.dump (dec, syn)
    in  dec
    end

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
          >>> removeEmptyEnv (syn, web)
          >>> unshare (syn, funtbl, looptbl)
          >>> analyze'n'flatten (syn, web)
          >>> allocate'n'expand (syn, web, funtbl, looptbl)
          >>> fixOvershare (syn, funtbl, looptbl)
          >>> segregateMLValues
          >>> removeSingletonEnv

        val decision = process (cps, syn)
        (* val () = print "FINAL\n" *)
        (* val () = ClosureDecision.dump (decision, syn) *)
    in  decision
    end
end
