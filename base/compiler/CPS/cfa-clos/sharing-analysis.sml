structure SharingAnalysis :> sig
  structure PackID : IDENTIFIER

  datatype pack = Pack of {
    packs: PackID.Set.set,
    loose: LambdaVar.Set.set,
    (* Invariant: disjointU (loose :: map #fv packs) = fv *)
    fv: LambdaVar.Set.set
  }

  type result = pack Group.Tbl.hash_table * pack PackID.Tbl.hash_table

  val analyze : LabelledCPS.function
              * SyntacticInfo.t
              * ControlFlow.funtbl
              * ControlFlow.looptbl
              -> result
end = struct
  structure PackID = IdentifierFn( )
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo
  structure W = Web
  structure Prob = Probability

  open ControlFlow

  datatype pack = Pack of {
    packs: PackID.Set.set,
    loose: LV.Set.set,
    fv: LV.Set.set (* Invariant: disjointU (packs, loose) = fv *)
  }

  type result = pack Group.Tbl.hash_table * pack PackID.Tbl.hash_table

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
    funtbl: funtbl,
    loopTbl: looptbl
  ) =
    let val lookupBlock = LCPS.FunTbl.lookup funtbl
        fun lookupLoopInfo block =
          Graph.NodeTbl.lookup loopTbl (Graph.Node block)
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


              (* val (usedFV, unusedFV) = LV.Set.partition (isUsed functions) fv *)

              (* TODO: Use a better heuristics *)
              val (packs, remainingFV) =
                let fun pick (candidates, chosen, remain) =
                      (case (candidates, LV.Set.isEmpty remain)
                         of (([], _) | (_, true)) => (chosen, fv)
                          | (c :: cs, _) =>
                              let fun szinter (_, Pack {fv, ...}) =
                                    let val inter =
                                          LV.Set.intersection (fv, remain)
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
              val loose =
                let val fv = foldl (fn ((_, Pack { fv, ... }), set) =>
                        LV.Set.difference (set, fv)
                      ) fv packs
                    val fv = LV.Set.listItems fv
                in  map (fn v => (v, defDepth v)) fv
                end

              val currDepth = S.depthOf syn (List.hd functions)

              val (packs, loose) =
                let val loose = sortBy #2 loose
                    val distCutoff = 3 and sizeCutoff = 3
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

              val result = Pack {
                  packs=PackID.Set.fromList (map #1 packs),
                  loose=LV.Set.fromList (map #1 loose),
                  fv=fv
                }
              (* val () = print "\n\n" *)
          in  insertGroup (grp, result); result
          end

        val () =
          let val fixes = sortFixes [lookupBlock cps]
              val packs = map ask fixes
          in  ()
          end

    in  (grpTbl, packTbl, replaceTbl)
    end

    (* TODO:
     * - If a pack is only used once, unpack it.
     * - Elide the pack that are the same.
     *)

    fun thin (
      grpTbl : pack Group.Tbl.hash_table,
      packTbl : pack PackID.Tbl.hash_table,
      syn : S.t
    ) =
    let val knownFun = S.knownFun syn
        fun packOf f = Group.Tbl.lookup grpTbl (S.groupOf syn f)
        fun thinning (Pack { loose, packs, fv }) =
          let fun go (v, (loose, packs)) =
                (case knownFun v
                   of NONE => (loose, packs)
                    | SOME f =>
                        let val Pack { packs=packsF, fv=fvF, ... } = packOf f
                            val loose = LV.Set.difference (loose, fvF)
                            val packs = PackID.Set.difference (packs, packsF)
                        in  (loose, packs)
                        end)
              val (loose, packs) =
                LV.Set.foldl go (loose, packs) fv
          in  Pack { loose=loose, packs=packs, fv=fv }
          end
        val () = Group.Tbl.modify thinning grpTbl
        val () = PackID.Tbl.modify thinning packTbl
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
        val useCountCutoff = 2
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
    funtbl: funtbl,
    loopTbl: looptbl
  ) : pack Group.Tbl.hash_table * pack PackID.Tbl.hash_table =
    let val (grpTbl, packTbl, replaceTbl) =
          preference (cps, syn, funtbl, loopTbl)
        val () = prune (grpTbl, packTbl, replaceTbl)
        val () = thin (grpTbl, packTbl, syn)

(*         val () = Group.Tbl.appi (fn (g, pack) => *)
(*           let val fs = S.groupFun syn g *)
(*               val name = String.concatWithMap "," (LV.lvarName o #2) *)
(*                                                   (Vector.toList fs) *)
(*           in  app print [name, " --> ", packToString pack, "\n"] *)
(*           end) grpTbl *)
(*         val () = print "==============\n" *)
(*         val () = PackID.Tbl.appi (fn (p, pack) => *)
(*           app print [PackID.toString p, " --> ", packToString pack, "\n"] *)
(*         ) packTbl *)
    in  (grpTbl, packTbl)
    end

    (* Generate a dot file *)
end
