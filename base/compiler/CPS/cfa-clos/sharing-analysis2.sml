structure SharingAnalysis2 :>
  SHARING_ANALYSIS where type pack = SharingAnalysis.pack
= struct
  (* structure PackID = IdentifierFn( ) *)
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo
  structure W = Web
  structure Prob = Probability
  structure Config = Control.NC

  structure CF = ControlFlow
  structure Graph = CF.Graph

  datatype usage = Accretion | Use of real | InLoopUse

  fun mergeUsage (Accretion, x)   = x
    | mergeUsage (x, Accretion)   = x
    | mergeUsage (Use p1, Use p2) = Use (p1 + p2)
    | mergeUsage (InLoopUse, x)   = InLoopUse
    | mergeUsage (x, InLoopUse)   = InLoopUse

  fun getProb (NONE, n)   = 1.0 / (real n)
    | getProb (SOME p, _) = Prob.toReal p


  fun analyzeUsage (
    syn: S.t,
    funtbl: CF.funtbl,
    looptbl: CF.looptbl,
    loopvars: CF.loopvartbl
  ) (f: LCPS.function): usage LV.Map.map =
    let val freevar = S.groupFV syn
        val union   = LV.Map.unionWith mergeUsage
        val insert  = LV.Map.insertWith mergeUsage
        fun getloopvar block =
          let val node = Graph.Node block
              val { header=loophdr, ty=ty, ... } =
                Graph.NodeTbl.lookup looptbl (Graph.Node block)
              val (loopvars, _) =
                (case (loophdr, ty)
                   of (Graph.Start _, CF.NonHeader) => (LV.Set.empty, [])
                    | (_, CF.NonHeader) => Graph.NodeTbl.lookup loopvars loophdr
                    | _ => Graph.NodeTbl.lookup loopvars node)
          in  loopvars
          end
        val entry  = LCPS.FunTbl.lookup funtbl f
        val loopvars = getloopvar entry
        fun walk (prob: real, b as CF.Block {term, fix, uses, ...}) =
          let val accretions = foldl (fn ((g, _), ac) =>
                  union (LV.Map.map (fn _ => Accretion) (freevar g), ac)
                ) LV.Map.empty fix
              val usages = LV.Set.foldl (fn (x, ac) =>
                  if LV.Set.member (loopvars, x) then
                    insert (ac, x, InLoopUse)
                  else
                    insert (ac, x, Use prob)
                ) accretions uses
          in  case term
                of CF.Branch (_, _, b1, b2, p) =>
                     let val p       = getProb (p, 2)
                         val usages1 = walk (prob * p, b1)
                         val usages2 = walk (prob * (1.0 - p), b2)
                     in  union (usages, union (usages1, usages2))
                     end
                 | CF.Switch blocks =>
                     let val n = List.length blocks
                     in  foldl (fn ((b, p), usages) =>
                           union (walk (getProb (p, n), b), usages)
                         ) usages blocks
                     end
                 | _ => usages
          end
        val fv     = S.groupFV syn (S.groupOf syn f)
        val usages = walk (1.0, entry)
    in  LV.Map.intersectWith (fn (u, _) => u) (usages, fv)
    end

  fun dumpUsage (f: LCPS.function, map: usage LV.Map.map) =
    let val (accretion, use, inloop) =
            LV.Map.foldli (fn
                (x, Accretion, (a, u, i)) => (x :: a, u, i)
              | (x, Use _, (a, u, i)) => (a, x :: u, i)
              | (x, InLoopUse, (a, u, i)) => (a, u, x :: i)
          ) ([], [], []) map
        fun plist xs =
          (print "[";
           print (String.concatWithMap "," LV.lvarName xs);
           print "]")
    in  print (LV.lvarName (#2 f) ^ ": ");
        print "\tA"; plist accretion;
        print "\tU"; plist use;
        print "\tI"; plist inloop;
        print "\n";
        ()
    end

  (* datatype pack = Pack of { *)
  (*   packs: PackID.Set.set, *)
  (*   loose: LV.Set.set, *)
  (*   fv: LV.Set.set (1* Invariant: disjointU (packs, loose) = fv *1) *)
  (* } *)
  datatype pack = datatype SharingAnalysis.pack

  (* type result = pack Group.Tbl.hash_table * pack PackID.Tbl.hash_table *)
  type result = SharingAnalysis.result

  fun packToString (Pack { packs, loose, fv }) =
    concat [
      "(packs=[",
      String.concatWithMap "," PackID.toString (PackID.Set.listItems packs),
      "], ",
      "loose=[",
      String.concatWithMap "," LV.lvarName (LV.Set.listItems loose),
      "], ",
      "fv=[", String.concatWithMap "," LV.lvarName (LV.Set.listItems fv), "])"
    ]

  fun samePack (
    Pack { packs=packs1, loose=loose1, ... },
    Pack { packs=packs2, loose=loose2, ... }
  ) = PackID.Set.equal (packs1, packs2) andalso LV.Set.equal (loose1, loose2)

  fun fvOfPack (Pack { fv, ... }) = fv
  fun disjointPack (p1, p2) = LV.Set.disjoint (fvOfPack p1, fvOfPack p2)

  fun sortBy (key : 'a -> int) (xs : 'a list) : 'a list =
    let fun gt (x, y) = key x > key y
    in  ListMergeSort.sort gt xs
    end

  fun removeMax (f : 'a -> int) (xs : 'a list) : 'a * 'a list =
    let fun go (pre, _, maxEl, []) = (maxEl, pre)
          | go (pre, maxN, maxEl, x :: xs) =
             let val currN = f x
             in  if currN > maxN then
                   let val (m, post) = go ([], currN, x, xs)
                   in  (m, maxEl :: pre @ post)
                   end
                 else
                   go (x :: pre, maxN, maxEl, xs)
             end
    in  case xs
          of [] => raise Empty
           | [x] => (x, [])
           | x :: xs => go ([], f x, x, xs)
    end

  (* Significance:
   *
   *
   * function p3 { packs=[p2], loose=[] }
   *   function p2: { packs=[p1], loose=[x] }
   *     Create p1 is only a move
   *
   * function p3 { packs=[p2], loose=[] }
   *   function p2: { packs=[p1], loose=[x] }
   *     Create p1 is only a move
   *)
   (* ask a fix what it wants
    *
    * Tile fv:
    *   Groups:
    *     id list
    *   Loose:
    *     fv list
    *   Function: group
    *
    *   GroupTbl: Group.id --> { groups, looseitems, total: fv list }
    *     invariant: reachable == fv
    *
    *   In a group, there are groups and ``loose items.'' Loose items can
    *   be converted to groups but groups cannot be touched.
    *
    * Leaf function:
    *   --> groups: {}, looseitems: fvs
    *
    * Non-leaf function:
    *   --> ask inner functions --> g: [groups, looseitems]
    *
    *   for each requested group:
    *   1. Propagate up
    *   2. Create here
    *   3. Find other groups
    *
    *   use groups to tile my fvs
    *   return groups: g, looseitems
    * *)

  (* TODO:
   * 1. Expansion may lead to some missed sharing opportunities. [FIXED]
   *
   * If a continuation variable is present in several closures, the current
   * heuristics will not put it in a pack because there is no point in boxing
   * one variable. But that variable will be expanded to 4 variables downstream.
   * It might actually be beneficial to group the 4 variables together. An
   * anticipatory size for each variable may be used to calculate the sizes of
   * packs.
   *
   * 2. Missed closure sharing opportunities from closing over recursive
   *    functions.
   *
   * If a function closes over its parent function (recursively), it can access
   * parts of its environment from the parent function.
   *)

  fun preference (
    cps: LCPS.function,
    syn: S.t,
    funtbl: CF.funtbl,
    looptbl: CF.looptbl,
    loopvars: CF.loopvartbl
  ) =
    let open ControlFlow
        val sizeCutoff = !Config.sharingSizeCutOff
        val distCutoff = !Config.sharingDistCutOff
        val lookupBlock = LCPS.FunTbl.lookup funtbl
        fun lookupLoopInfo block =
          Graph.NodeTbl.lookup looptbl (Graph.Node block)
        fun isUsed fs v =
          List.exists (fn f => LCPS.FunSet.member (S.useSites syn v, f)) fs
        fun sortFixes blocks =
          let fun walk (prob, b as Block { term, fix, ... }) =
                let val { nestingDepth, ... } = lookupLoopInfo b
                    val curr = map (fn f => (f, nestingDepth, prob)) fix
                in  case term
                      of Branch (_, _, b1, b2, probOpt) =>
                           let val (prob1, prob2) =
                                 case probOpt
                                   of SOME p =>
                                        (Prob.toReal p,
                                         Prob.toReal (Prob.not p))
                                    | NONE => (0.5, 0.5)
                           in  curr @ walk (prob * prob1, b1)
                                    @ walk (prob * prob2, b2)
                           end
                       | Switch blocks =>
                           let val defaultProb =
                                 1.0 / Real.fromInt (List.length blocks)
                               fun getOpt (SOME p) = Prob.toReal p
                                 | getOpt NONE = defaultProb
                           in  foldl (fn ((b, p), fixes) =>
                                 walk (prob * getOpt p, b) @ fixes
                               ) curr blocks
                           end
                        | _ => curr
                end
              val fixes = List.concatMap (fn b => walk (1.0, b)) blocks
              fun gt ((_, l1, p1), (_, l2, p2)) =
                if l1 = l2 then p1 < p2 else l1 < l2
          in  map #1 (ListMergeSort.sort gt fixes)
          end
        fun introducedAt (fs: LCPS.function list) v =
          let val defsite = S.defSite syn v
          in  List.exists (fn f => LV.same (#2 f, v) orelse LV.same (#2 f, #2 defsite)) fs
          end

        val packTbl = PackID.Tbl.mkTable (S.numFuns syn, Fail "pack table")
        val insertPack = PackID.Tbl.insert packTbl
        val lookupPack = PackID.Tbl.lookup packTbl
        val findPack = PackID.Tbl.find packTbl

        val grpTbl = Group.Tbl.mkTable (S.numFuns syn, Fail "grp table")
        val insertGroup = Group.Tbl.insert grpTbl
        val lookupGroup = Group.Tbl.lookup grpTbl

        val pinnedTbl = Group.Tbl.mkTable (S.numFuns syn, Fail "pinned table")
        val insertPin = Group.Tbl.insert pinnedTbl
        val lookupPin = Group.Tbl.lookup pinnedTbl

        val getUsage   = analyzeUsage (syn, funtbl, looptbl, loopvars)
        val unionUsage = LV.Map.unionWith mergeUsage

        val replaceTbl = PackID.Tbl.mkTable (64, Fail "replace table")
        fun replace (from, to) =
          (case PackID.Tbl.find replaceTbl from
             of SOME _ => raise Fail "Double replacement"
              | NONE   => PackID.Tbl.insert replaceTbl (from, to))

        fun setOfKeys (map: 'a LV.Map.map) : LV.Set.set =
          let val keys = LV.Map.listKeys map
          in  LV.Set.fromList keys
          end

        fun allPacks ([], result) = result
          | allPacks (Pack { packs, ... }::ps, result) =
              let val packs = PackID.Set.foldl (fn (p, res) =>
                    (p, lookupPack p) :: res
                  ) result packs
              in  allPacks (ps, packs)
              end

        fun defDepth v = S.depthOf syn (S.defSite syn v)

        fun mkPack (fs : LCPS.function list) data =
          let val name = String.concatWithMap "-" (LV.lvarName o #2) fs
              val packID = PackID.new name
              val pack = Pack data
          in  insertPack (packID, pack); (packID, pack)
          end

        fun ask (grp: Group.t, functions: LCPS.function list) : pack =
          let val blocks = map lookupBlock functions
              val fv     = setOfKeys (S.groupFV syn grp)
              val usage  = foldl (fn (f, u) =>
                  unionUsage (getUsage f, u)
                ) LV.Map.empty functions
              val fixes  = sortFixes blocks
              val packs  = map ask fixes
              val lowerLevelPacks = allPacks (packs, [])

              (* val () = *)
              (*   let val name = String.concatWithMap "," (LV.lvarName o #2) *)
              (*                                        functions *)
              (*   in  app print ["IN FUNCTIONS ", name, "\n"] *)
              (*   end *)

              (* See if we can throw any of the lower-level packs up since if
               * not we are responsible for allocating the pack. *)
              val (ineligibles, candidates) =
                List.partition (fn (_, Pack { fv, ... }) =>
                  LV.Set.exists (introducedAt functions) fv
                ) lowerLevelPacks

              (* val () = *)
              (*   app print [ *)
              (*   "candidates=[", String.concatWithMap ", " *)
              (*   (PackID.toString o #1) candidates, "]\n", *)
              (*   "ineligibles=[", String.concatWithMap ", " *)
              (*   (PackID.toString o #1) ineligibles, "]\n"] *)

              val (loopFV, computeFV, unusedFV) =
                LV.Set.foldl (fn (v, (l, c, u)) =>
                  (case LV.Map.find (usage, v)
                     of NONE => raise Fail "Incomprehensive usage map"
                      | SOME InLoopUse => (LV.Set.add (l, v), c, u)
                      | SOME (Use _)   => (l, LV.Set.add (c, v), u)
                      | SOME Accretion => (l, c, LV.Set.add (u, v)))
                ) (LV.Set.empty, LV.Set.empty, LV.Set.empty) fv
              (* loopFV -- we are currently in a loop and this is a loop
               *           invariant.
               * computeFV -- this fv is used directly for computation
               * unusedFV  -- this fv is captured for a nested function
               *
               * loopFV will be not be put into a shared record. *)

              (* TODO: Use a better heuristics *)
              val (packs, remainingFV) =
                let fun pick (candidates, chosen, remain) =
                      (case (candidates, LV.Set.isEmpty remain)
                         of (([], _) | (_, true)) => (chosen, fv)
                          | (c :: cs, _) =>
                              let fun szinter (_, Pack {fv, ...}) =
                                    let val inter =
                                          LV.Set.intersection (fv, unusedFV)
                                    in  LV.Set.numItems inter
                                    end
                                  val (c, cs) = removeMax szinter (c :: cs)
                                  val remain =
                                    let val (_, Pack { fv, ... }) = c
                                    in  LV.Set.difference (remain, fv)
                                    end
                                  (* TODO: This disallows duplication. *)
                                  val cs = List.filter (fn (_, c') =>
                                    disjointPack (#2 c, c')) cs
                              in  pick (cs, c :: chosen, remain)
                              end)
                in  pick (candidates, [], fv)
                end

              val rejected =
                let fun inPacks (p, _) =
                      List.exists (fn (p', _) => PackID.same (p, p')) packs
                in  List.filter (not o inPacks) candidates
                end

              (* val () = *)
              (*   app print [ *)
              (*   "picked=[", String.concatWithMap ", " *)
              (*   (PackID.toString o #1) packs, "]\n", *)
              (*   "rejected=[", String.concatWithMap ", " *)
              (*   (PackID.toString o #1) rejected, "]\n"] *)


              val () =
                let fun replaceIfSame ((packid1, pack1), (packid2, pack2)) =
                      if PackID.same (packid1, packid2) then
                        raise Fail (PackID.toString packid1 ^ "?????")
                      else if samePack (pack1, pack2) then
                        replace (packid1, packid2)
                      else
                        ()
                    fun checkDup rejected =
                      app (fn c => replaceIfSame (rejected, c)) packs

                    (* val () = app print ["#rejected=", Int.toString (List.length *)
                    (* rejected), "\n"] *)
                in  app checkDup rejected
                end

              (* These are the free variables that the packs have not
               * accounted for. *)
              val (remainingCompute, remainingUnused) =
                let val (compute, unused) =
                      foldl (fn ((_, Pack { fv, ... }), (c, u)) =>
                        (LV.Set.difference (c, fv), LV.Set.difference (u, fv))
                      ) (computeFV, unusedFV) packs
                    (* val compute = LV.Set.listItems compute *)
                    val unused  = LV.Set.listItems unused
                in  (compute,
                     map (fn v => (v, defDepth v)) unused)
                end

              val currDepth = S.depthOf syn (List.hd functions)

              val (packs, looseUnusedAndCompute) =
                let val loose = sortBy #2 remainingUnused
                    fun findCandidatePacks (vs, fstDepth, currPack, packs) =
                      (case vs
                         of [] => currPack :: packs
                          | (v as (_, d)) :: vs =>
                              if d - fstDepth > distCutoff then
                                findCandidatePacks
                                  (vs, d, [v], currPack :: packs)
                              else
                                findCandidatePacks
                                  (vs, fstDepth, v :: currPack, packs))
                    val candidatePacks : (CPS.lvar * int) list list =
                      (case loose
                         of [] => []
                          | (v as (_, d)) :: vs =>
                              findCandidatePacks (vs, d, [v], []))
                    fun packSize pack =
                      let fun sz (v, _) =
                            (case (S.knownFun syn v, S.typeof syn v)
                               of (SOME _, CPS.CNTt) => 3
                                | (NONE, CPS.CNTt) => 4
                                | _ => 1)
                      in  foldl (fn (v, sum) => sz v + sum) 0 pack
                      end
                    val (chosen, rejected) =
                      List.partition
                        (fn pack => packSize pack >= sizeCutoff)
                        candidatePacks
                    val loose = List.concat rejected
                    val packs =
                      foldl (fn (pack, packs) =>
                        let val loose = LV.Set.fromList (map #1 pack)
                            val newpack =
                              mkPack functions {
                                  packs=PackID.Set.empty,
                                  loose=loose,
                                  fv=loose
                                }
                        in  newpack :: packs
                        end
                      ) packs chosen
                in  (packs, loose)
                end

              val loose = LV.Set.union (
                LV.Set.fromList (map #1 looseUnusedAndCompute),
                LV.Set.union (remainingCompute, loopFV)
              )

              val result = Pack {
                  packs=PackID.Set.fromList (map #1 packs),
                  loose=loose,
                  fv=fv
                }
              (* val () = print "\n\n" *)
          in  insertGroup (grp, result);
              insertPin (grp, loopFV);
              result
          end

        val () =
          let val fixes = sortFixes [lookupBlock cps]
              val packs = map ask fixes
          in  ()
          end

    in  (grpTbl, packTbl, replaceTbl, pinnedTbl)
    end

    (* TODO:
     * - If a pack is only used once, unpack it.
     * - Elide the pack that are the same.
     *)

    (* NOTE: after thinning, some packs may drop below the size cut off *)

    fun thin (
      grpTbl : pack Group.Tbl.hash_table,
      packTbl : pack PackID.Tbl.hash_table,
      pinnedTbl : LV.Set.set Group.Tbl.hash_table,
      syn : S.t
    ) =
    let val knownFun = S.knownFun syn
        fun packOf f = Group.Tbl.lookup grpTbl (S.groupOf syn f)
        val lookupPack = PackID.Tbl.lookup packTbl
        val lookupPin  = Group.Tbl.lookup pinnedTbl
        (* fun reachableInDepthN (n, Pack { packs, loose, ... }) = *)
        (*   let datatype either = datatype Either.either *)
        (*       fun go ([], packs, loose) = (packs, loose) *)
        (*         | go ((depth, INL pack) :: todo, packs, loose) = *)
        (*             if depth <= n - 1 then *)
        (*               let val Pack { packs=packsP, loose=looseP, ... } = *)
        (*                     lookupPack pack *)
        (*                   val todop = map (fn p => (depth + 1, INL p)) packsP *)
        (*                   val todol = map (fn l => (depth + 1, INR l)) looseP *)
        (*                   val packs = PackID.Set.insert (packs, pack) *)
        (*               in  go (todop @ todol @ todo, packs, loose) *)
        (*               end *)
        (*             else *)
        (*               go (todo, PackID.Set.insert (packs, pack), loose) *)
        (*         | go ((depth, INR v) :: todo, packs, loose) = *)
        (*             (case knownFun v *)
        (*                of NONE   => go (todo, packs, LV.Set.insert (loose, v)) *)
        (*                 | SOME f => *)
        (*                     if depth <= n - 1 then *)
        (*                       let val Pack { packs=packsF, loose=looseF, ... } = *)
        (*                             packOf f (1* NB: f's layout is decided *1) *)
        (*                           val todop = *)
        (*                             map (fn p => (depth + 1, INL p)) packsF *)
        (*                           val todol = *)
        (*                             map (fn p => (depth + 1, INL l)) looseF *)
        (*                       in  go (todop @ todol @ todo, packs, *)
        (*                               LV.Set.insert (loose, v)) *)
        (*                       end) *)
        (*       val todop = map (fn p => (1, INL p)) packs *)
        (*       val todol = map (fn l => (1, INR l)) loose *)
        (*   in  go (todop @ todol, PackID.Set.empty, LV.Set.empty) *)
        (*   end *)

        fun thinning (pinned, Pack { loose, packs, fv }) =
          let fun go (v, (loose, packs)) =
                (case knownFun v
                   of NONE => (loose, packs)
                    | SOME f =>
                        let val Pack { packs=packsF, fv=looseF, ... } =
                              packOf f
                            val looseF = LV.Set.difference (looseF, pinned)
                            val loose = LV.Set.difference (loose, looseF)
                            val packs = PackID.Set.difference (packs, packsF)
                        in  (loose, packs)
                        end)
              val (loose, packs) =
                LV.Set.foldl go (loose, packs) fv
          in  Pack { loose=loose, packs=packs, fv=fv }
          end
        val () =
          Group.Tbl.modifyi (fn (g, pck) => thinning (lookupPin g, pck)) grpTbl
        val () =
          PackID.Tbl.modify (fn pck => thinning (LV.Set.empty, pck)) packTbl
    in  ()
    end

    fun prune (
      grpTbl : pack Group.Tbl.hash_table,
      packTbl : pack PackID.Tbl.hash_table,
      replaceTbl : PackID.t PackID.Tbl.hash_table
    ) =
    let
        (* Step 1: Figure out what packs are the same *)
        (* val replaceMap : PackID.t PackID.Map.map = *)
        (*   (1* TODO: Do this faster than n^2 ? *1) *)
        (*   PackID.Tbl.foldi (fn (packid1, pack1, map) => *)
        (*     PackID.Tbl.foldi (fn (packid2, pack2, map) => *)
        (*       if not (PackID.Map.inDomain (map, packid1)) *)
        (*          andalso not (PackID.same (packid1, packid2)) *)
        (*          andalso samePack (pack1, pack2) then *)
        (*         PackID.Map.insert (map, packid2, packid1) *)
        (*       else *)
        (*         map *)
        (*     ) map packTbl *)
        (*   ) PackID.Map.empty packTbl *)

        fun replace packid =
          (case PackID.Tbl.find replaceTbl packid
             of SOME packid' =>
                  let val root = replace packid'
                  in  PackID.Tbl.insert replaceTbl (packid, root); root
                  end
              | NONE => packid)

        fun replacePack (Pack {packs, loose, fv}) =
          let val packs = PackID.Set.map replace packs
          in  Pack { packs=packs, loose=loose, fv=fv }
          end

        (* val () = PackID.Tbl.appi (fn (p1, p2) => *)
        (*   app print [PackID.toString p1, " ----> ", PackID.toString p2, "\n"] *)
        (* ) replaceTbl *)

        val () = Group.Tbl.modify replacePack grpTbl

        (* Step 2: Clean up unused or unshared packs *)
        val useCountCutoff = !Config.sharingUseCutOff
        datatype usage = Unused
                       | UsedOnlyBy of Group.t list
                       (* Items used more than once are cleared out of the
                        * table *)
        val usageTbl = PackID.Tbl.map (fn _ => Unused) packTbl
        fun use grp pack =
          (case PackID.Tbl.find usageTbl pack
             of NONE => ()
              | SOME Unused =>
                  PackID.Tbl.insert usageTbl (pack, UsedOnlyBy [grp])
              | SOME (UsedOnlyBy []) => raise Fail "impossible"
              | SOME (UsedOnlyBy grps) =>
                  if List.length grps < useCountCutoff then
                    PackID.Tbl.insert usageTbl (pack, UsedOnlyBy (grp :: grps))
                  else
                    ignore (PackID.Tbl.remove usageTbl pack))

        val () = Group.Tbl.appi (fn (grp, Pack { packs, ... }) =>
            PackID.Set.app (use grp) packs
          ) grpTbl

        (* NOTE: Currently, packs don't have other packs, so we don't need to
         * scan the packTbl. If that changes in the future, scan it. *)

        fun flattenIn pckid grp =
          let val Pack { packs, loose, fv } = Group.Tbl.lookup grpTbl grp
              val packs = PackID.Set.delete (packs, pckid)
              val pack  = PackID.Tbl.lookup packTbl pckid
              val loose = LV.Set.union (loose, fvOfPack pack)
              val newpack = Pack { packs=packs, loose=loose, fv=fv }
          in  Group.Tbl.insert grpTbl (grp, newpack)
          end

        val () = PackID.Tbl.appi (fn (pckid, usage) =>
            (case usage
               of Unused => ignore (PackID.Tbl.remove packTbl pckid)
                | UsedOnlyBy grps =>
                    (app (flattenIn pckid) grps;
                     ignore (PackID.Tbl.remove packTbl pckid)))
           ) usageTbl
    in  ()
    end

  fun analyze (
    cps: LCPS.function,
    syn: S.t,
    funtbl: CF.funtbl,
    looptbl: CF.looptbl,
    loopvartbl: CF.loopvartbl
  ) : pack Group.Tbl.hash_table * pack PackID.Tbl.hash_table =
    let val (grpTbl, packTbl, replaceTbl, pinnedTbl) =
          preference (cps, syn, funtbl, looptbl, loopvartbl)
        val () = prune (grpTbl, packTbl, replaceTbl)
        val () =
          if !Config.sharingNoThinning then
            ()
          else
            thin (grpTbl, packTbl, pinnedTbl, syn)

        (* val () = Group.Tbl.appi (fn (g, pack) => *)
        (*   let val fs = S.groupFun syn g *)
        (*       val name = String.concatWithMap "," (LV.lvarName o #2) *)
        (*                                           (Vector.toList fs) *)
        (*   in  app print [name, " --> ", packToString pack, "\n"] *)
        (*   end) grpTbl *)
        (* val () = print "==============\n" *)
        (* val () = PackID.Tbl.appi (fn (p, pack) => *)
        (*   app print [PackID.toString p, " --> ", packToString pack, "\n"] *)
        (* ) packTbl *)

        (* fun appF f = Vector.app (fn g => *)
        (*   let val fs = S.groupFun syn g *)
        (*   in  Vector.app f fs *)
        (*   end) (S.groups syn) *)
        (* val () = appF (fn f => *)
        (*     let val usage = analyzeUsage (syn, funtbl, looptbl, loopvars) f *)
        (*     in  dumpUsage (f, usage) *)
        (*     end *)
        (*   ) *)
        (* val () = ControlFlow.Graph.NodeTbl.appi (fn (node, (lv, inners)) => *)
        (*     (print (ControlFlow.Graph.nodeToString node ^ "\n"); *)
        (*      app print [ *)
        (*        "\t[", *)
        (*        String.concatWithMap "," LV.lvarName (LV.Set.listItems lv), *)
        (*        "]\n"]; *)
        (*      app print [ *)
        (*        "\tinner [", *)
        (*        String.concatWithMap "," ControlFlow.Graph.nodeToString inners, *)
        (*        "]\n" *)
        (*       ]) *)
        (*   ) loopvars *)
    in  (grpTbl, packTbl)
    end


end
