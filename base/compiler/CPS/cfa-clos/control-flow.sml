structure ControlFlow :> sig
  val analyze : LabelledCPS.function * SyntacticInfo.t * FlowCFA.result -> unit
end = struct
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo
  structure W = Web

  (* This module comes from MLRISC library. *)
  structure Prob = Probability
  type prob = Prob.prob

  datatype terminator
    = Return of CPS.lvar * CPS.value list
    | Call   of CPS.lvar * CPS.value list
    | Raise  of CPS.lvar * CPS.value list
    | Branch of CPS.P.branch * CPS.value list * block * block * prob option
    | Switch of (block * prob option) list
  and block = Block of {
      term: terminator,
      label: LCPS.label,
      fix: fix list,
      function: LCPS.function
    }
  withtype fix = Group.t * LCPS.function list

  type funtbl = block LCPS.FunTbl.hash_table

  fun terminatorName (Return _) = "return"
    | terminatorName (Call _) = "call"
    | terminatorName (Raise _) = "raise"
    | terminatorName (Branch _) = "branch"
    | terminatorName (Switch _) = "switch"

  structure Summary :> sig
    val analyze : S.t -> funtbl
  end = struct
    structure P = CPS.P

    datatype var_info
      = Length
      | Handler

    (* Ball-Larus branch probability.
     *     Wu, Larus. "Static branch frequency and program profile analysis"
     *)
    val PH = Prob.percent 80          val notPH = Prob.not PH
    val OH = Prob.percent 84          val notOH = Prob.not OH
    val RH = Prob.percent 72          val notRH = Prob.not RH
    val unlikely = Prob.prob (1, 100) val likely = Prob.not unlikely

    fun predict (lookup, test, args, block1, block2) : prob option =
      let fun combine (f, prob) =
            (case (f (), prob)
               of (NONE, NONE) => NONE
                | (NONE, p as SOME _) => p
                | (p as SOME _, NONE) => p
                | (SOME takenP, SOME trueP) =>
                    let val prob =
                          Prob.combineProb2 {trueProb=trueP, takenProb=takenP}
                    in  SOME (#t prob)
                    end)
          val Block {term=term1, ...} = block1
          val Block {term=term2, ...} = block2

          (* Pointer heuristic (PH): Predict that a comparison of a pointer
           * against null or of two pointers will fail *)
          fun ph () =
            (case test
               of P.BOXED => SOME PH
                | P.UNBOXED => SOME notPH
                | P.PEQL => SOME notPH
                | P.PNEQ => SOME PH
                | _ => NONE)

          (* Opcode heuristic (OH): Predict that a comparison of an integer for
           * less than zero, less than or equal to zero, or equal to a constant
           * will fail. In SML, floats and strings behave sort of like an
           * integer, so I apply this heuristics to those as well. *)
          fun oh () =
            let datatype num = Zero | Constant | Register
                fun number (CPS.NUM {ival=0, ...}) = Zero
                  | number (CPS.NUM _) = Constant
                  | number (CPS.REAL {rval, ...}) =
                      if RealLit.isZero rval then Zero else Constant
                  | number _ = Register
            in  case (test, args)
                  of (P.CMP {oper, ...}, [v1, v2]) =>
                       (case (oper, number v1, number v2)
                          of (P.LT, _, Zero) => SOME notOH
                           | (P.LTE, _, Zero) => SOME notOH
                           | (P.EQL, _, Constant) => SOME notOH

                           | (P.LT, Zero, _) => SOME OH
                           | (P.LTE, Zero, _) => SOME OH
                           | (P.EQL, Constant, _) => SOME notOH

                           | (P.GT, _, Zero) => SOME OH
                           | (P.GTE, _, Zero) => SOME OH
                           | (P.NEQ, _, Constant) => SOME OH

                           | (P.GT, Zero, _) => SOME notOH
                           | (P.GTE, Zero, _) => SOME notOH
                           | (P.NEQ, Constant, _) => SOME OH
                           | _ => NONE)
                   | (P.FCMP {oper, ...}, [v1, v2]) =>
                       (case (oper, number v1, number v2)
                          of ((P.F_LT | P.F_ULT), _, Zero) => SOME notOH
                           | ((P.F_LE | P.F_ULE), _, Zero) => SOME notOH
                           | ((P.F_EQ | P.F_UE), _, Constant) => SOME notOH

                           | ((P.F_LT | P.F_ULT), Zero, _) => SOME OH
                           | ((P.F_LE | P.F_ULE), Zero, _) => SOME OH
                           | ((P.F_EQ | P.F_UE), Constant, _) => SOME notOH

                           | ((P.F_GT | P.F_UGT), _, Zero) => SOME OH
                           | ((P.F_GE | P.F_UGE), _, Zero) => SOME OH
                           | ((P.F_LG | P.F_ULG), _, Constant) => SOME OH

                           | ((P.F_GT | P.F_UGT), Zero, _) => SOME notOH
                           | ((P.F_GE | P.F_UGE), Zero, _) => SOME notOH
                           | ((P.F_LG | P.F_ULG), Constant, _) => SOME OH
                           | _ => NONE)
                   | (P.STREQL _, _) => SOME notOH
                   | _ => NONE
            end

          (* NOTE: If one of the branches is itself a branch, these heuristics
           * will not apply. Maybe we can add a ``characteristics'' property to
           * a Branch that states what this branch will likely do to return *)

          (* Return heuristic (RH): Predict a successor that contains a return
           * will not be taken *)
          fun rh () =
            (case (term1, term2)
               of (Return _, Return _) => NONE
                | (Return _, Call _) => SOME notRH
                | (Call _, Return _) => SOME RH
                | _ => NONE)

          (* Miscellaneous:
           * 1. Predict that if a branch that throws exception will not be taken
           * 2. Predict that boundsCheck will succeed.
           *)
          fun raiseExn () =
            (case (term1, term2)
               of (Raise _, _) => SOME unlikely
                | (_, Raise _) => SOME likely
                | _ => NONE)

          fun boundsCheck () =
            (case (test, args)
               of (P.CMP {oper=P.LT, ...}, [v1, CPS.VAR v2]) =>
                    (case lookup v2
                       of SOME Lenght => SOME likely
                        | _ => NONE)
                | _ => NONE)

          val heuristics = [ph, oh, rh, raiseExn, boundsCheck]
      in  foldl combine NONE heuristics
      end

    fun calculate (f: LCPS.function, syn: S.t): block =
      let val info = LV.Tbl.mkTable (32, Fail "info table")
          val insertInfo = LV.Tbl.insert info
          val lookupInfo = LV.Tbl.find info
          val typeof = S.typeof syn
          fun walk (LCPS.APP (l, CPS.VAR v, args)) =
                let val term =
                      (case typeof v
                         of CPS.CNTt => Return (v, args)
                          | _ => (case lookupInfo v
                                    of SOME Handler => Raise (v, args)
                                     | _ => Call (v, args)))
                in  Block { term=term, fix=[], label=l, function=f }
                end
            | walk (LCPS.APP (_, _, _)) = raise Fail "App non arg"
            | walk (LCPS.FIX (l, functions, exp)) =
                let val Block { term, fix, label, function } = walk exp
                in  Block {
                      term=term,
                      fix=(Group.wrap l, functions)::fix,
                      label=label,
                      function=function
                    }
                end
            | walk (LCPS.BRANCH (l, branch, args, _, exp1, exp2)) =
                let val blk1 = walk exp1
                    val blk2 = walk exp2
                    val prob = predict (lookupInfo, branch, args, blk1, blk2)
                    val term = Branch (branch, args, blk1, blk2, prob)
                in  Block { term=term, fix=[], label=l, function=f }
                end
            | walk (LCPS.SWITCH (l, _, _, exps)) =
                let (* TODO: multi-arm branch prediction?
                     *
                     * The problem with SWITCH in the CPS IR is that there is no
                     * information on the SWITCH argument --- it is just an
                     * integer. The only heuristics that could apply is RH, and
                     * I'm not sure how useful it is. *)
                    val blocks = map (fn e => (walk e, NONE)) exps
                in  Block { term=Switch blocks, fix=[], label=l, function=f }
                end
            | walk (LCPS.PURE (_, (CPS.P.OBJLENGTH|CPS.P.LENGTH), _, x, _, e)) =
                (insertInfo (x, Length); walk e)
            | walk (LCPS.PURE (_, _, _, _, _, exp)) = walk exp
            | walk (LCPS.LOOKER (_, CPS.P.GETHDLR, _, x, _, e)) =
                (insertInfo (x, Handler); walk e)
            | walk (LCPS.LOOKER (_, _, _, _, _, exp)) = walk exp
            | walk (LCPS.RECORD (_, _, _, _, exp)) = walk exp
            | walk (LCPS.SELECT (_, _, _, _, _, exp)) = walk exp
            | walk (LCPS.OFFSET (_, _, _, _, exp)) = walk exp
            | walk (LCPS.SETTER (_, _, _, exp)) = walk exp
            | walk (LCPS.ARITH  (_, _, _, _, _, exp)) = walk exp
            | walk (LCPS.RCC (_, _, _, _, _, _, exp)) = walk exp
          val (_, _, _, _, cexp) = f
      in  walk cexp
      end

    fun analyze (syn: S.t) =
      let val funtbl = LCPS.FunTbl.mkTable (S.numFuns syn, Fail "funtbl")
          val insert = LCPS.FunTbl.insert funtbl
          fun calculateAndInsert f =
            let val block = calculate (f, syn)
            in  insert (f, block)
            end
          val () = S.appF syn calculateAndInsert
          val () = calculateAndInsert (S.topLevel syn)
      in  funtbl
      end
  end

  (* Graph:
   * node = Start | Block of block
   * edge = Local | Precise | Imprecise | Fake
   *)

  structure Graph :> sig
    datatype node = Start of LCPS.label | Node of block
    datatype edge
      = Local of block list * prob option
      | Precise of block list
      | Imprecise of block list
      | Fake of block list

    structure NodeTbl : MONO_HASH_TABLE where type Key.hash_key = node

    type t
    val build : funtbl * S.t * FlowCFA.result -> t

    val root  : t -> node
    val succ  : t * node -> node list
    val succ' : t * node -> block list
    val pred  : t * node -> node list

    val appPred : t * (node * node list -> unit) -> unit

    val numNodes : t -> int
    val nodeToString : node -> string

    val dumpDot : t -> unit
    val dumpDot' : t * (node -> string) -> unit
  end = struct

    datatype node = Start of LCPS.label | Node of block
    datatype edge
      = Local of block list * prob option
      | Precise of block list
      | Imprecise of block list
      | Fake of block list

    fun nodeLabel (Start label) = label
      | nodeLabel (Node (Block {label, ...})) = label

    fun sameNode (Start _, Start _) = true
      | sameNode (
          Node (Block {label=label1, ...}),
          Node (Block {label=label2, ...})
        ) = LV.same (label1, label2)
      | sameNode _ = false

    fun destsOfEdge (Local (dests, _) | Precise dests |
                     Imprecise dests | Fake dests) = dests

    structure NodeTbl : MONO_HASH_TABLE = HashTableFn(struct
      type hash_key = node
      val hashVal = LV.Tbl.Key.hashVal o nodeLabel
      val sameKey = sameNode
    end)

    datatype t = Graph of {
      start  : node,
      funtbl : funtbl,
      succ   : edge NodeTbl.hash_table,
      pred   : node list NodeTbl.hash_table
    }

    fun appendUniq ([], node) = [node]
      | appendUniq (n :: ns, node) =
          if sameNode (n, node) then n :: ns else n :: appendUniq (ns, node)

    fun build (funtbl: funtbl, syn: S.t, {lookup, flow}: FlowCFA.result) : t =
      let val succ : edge      NodeTbl.hash_table =
            NodeTbl.mkTable (2 * S.numFuns syn, Fail "succ")
          val pred : node list NodeTbl.hash_table =
            NodeTbl.mkTable (2 * S.numFuns syn, Fail "succ")

          val entryBlock = LCPS.FunTbl.lookup funtbl

          fun insertSucc (src, dests) =
            case NodeTbl.find succ src
              of SOME _ => raise Fail "Multiple insertion"
               | NONE => NodeTbl.insert succ (src, dests)


          fun insertPred (dest, src) =
            case NodeTbl.find pred dest
              of SOME srcs =>
                   NodeTbl.insert pred (dest, appendUniq (srcs, src))
               | NONE =>
                   NodeTbl.insert pred (dest, [src])

          fun addEdge (src, edge) =
            let val () = insertSucc (src, edge)
                val dests = destsOfEdge edge
                val () = app (fn dest => insertPred (Node dest, src)) dests
            in  ()
            end

          fun blocksOfValue (CPS.VAR v) : block list =
                (case lookup v
                   of NONE => []
                    | SOME { unknown=true, ... } => []
                    | SOME { known, ... } => map entryBlock known)
            | blocksOfValue _ = []

          fun processB (src as Block { term, ... }) =
            (case term
               of (Return (f, args) | Call (f, args) | Raise (f, args)) =>
                    (case lookup f
                       of NONE => addEdge (Node src, Imprecise [])
                        | SOME { unknown=true, known=[] } =>
                            (* If f is calling nothing but unknown
                             * functions, the assumption is that the
                             * unknown functions will call any
                             * continuations/functions passed in. *)
                            let val fake = List.concatMap blocksOfValue args
                            in  addEdge (Node src, Fake fake)
                            end
                        | SOME { unknown=true, known } =>
                            addEdge (Node src, Imprecise (map entryBlock known))
                        | SOME { unknown=false, known } =>
                            addEdge (Node src, Precise (map entryBlock known)))
                | Branch (_, _, block1, block2, prob) =>
                    (addEdge (Node src, Local ([block1, block2], prob));
                     processB block1;
                     processB block2)
                | Switch blocks =>
                    (addEdge (Node src, Local (map #1 blocks, NONE));
                     app (processB o #1) blocks))

          val () = LCPS.FunTbl.app processB funtbl
          val start = Start (#2 (S.topLevel syn))
                      (* Arbitrary unique label for start node *)
          fun collectBlock (f, block, acc) =
            (case flow f
               of { escape=true, ... } => block :: acc
                | _ => acc)

          val escapingBlocks =
            LCPS.FunTbl.foldi
              (fn (f, block, acc) => collectBlock (f, block, acc)) [] funtbl
          val () = addEdge (start, Fake escapingBlocks)
      in  Graph { start=start, funtbl=funtbl, succ=succ, pred=pred }
      end

    fun root (Graph { start, ... }) = start
    fun succ' (Graph { succ=succTbl, ... }, n) =
      destsOfEdge (NodeTbl.lookup succTbl n)
    fun succ (graph, n) = map Node (succ' (graph, n))
    fun pred (Graph { pred=predTbl, ... }, n) = NodeTbl.lookup predTbl n

    fun appPred (Graph { pred=predTbl, ... }, f) = NodeTbl.appi f predTbl

    fun numNodes (Graph { succ, ... }) = NodeTbl.numItems succ

    fun nodeToString (Start _) = "START"
      | nodeToString (Node (Block { label, function, ... })) =
          ("B" ^ LV.lvarName label ^ "[" ^ LV.lvarName (#2 function) ^ "]")

    local open DotLanguage in
      fun dumpDot' (Graph { start, funtbl, succ, pred }, ann) =
        let val nodeId = LV.lvarName o nodeLabel
            fun blockId (Block {label, ...}) = LV.lvarName label
            fun probToS p = Real.fmt (StringCvt.FIX (SOME 3)) (Prob.toReal p)
            fun addEdges (src, edge, dot) =
              let val dests =
                    (case edge
                       of Precise dests =>
                            map (fn d => (d, [])) dests
                        | Imprecise dests  =>
                            map (fn d => (d,  [("style", "dashed")])) dests
                        | Fake dests =>
                            map (fn d => (d,
                                  [("style", "dashed"), ("color", "red"),
                                   ("constraint", "false")])) dests
                        | Local ([b1, b2], SOME prob) =>
                            [(b1, [("style", "bold"), ("label", probToS prob)]),
                             (b2, [("style", "bold"),
                                   ("label", probToS (Prob.not prob))])]
                        | Local (dests, _) =>
                            map (fn d => (d, [("style", "bold")])) dests)
              in  foldl (fn ((dst, attrs), dot) =>
                    << (dot, EDGE (nodeId src, blockId dst, attrs))) dot
                    dests
              end
            fun addFunCluster (f: LCPS.function, block, dot) =
              let fun blocknode (b as Block {label, term, ...}) : stmt =
                    NODE (LV.lvarName label,
                          [("label", terminatorName term ^ ann (Node b)),
                           ("shape", "box")])
                  fun walk (b as Block {term, ...}) : stmt list =
                    (case term
                       of Branch (_, _, b1, b2, _) =>
                            blocknode b :: walk b1 @ walk b2
                        | Switch blocks =>
                            blocknode b :: List.concatMap (walk o #1) blocks
                        | _ => [blocknode b])
                  val fname = LV.lvarName (#2 f)
                  val stmts = ATTR "graph[style=dotted]"
                           :: ATTR (concat ["label=\"", fname, "\""])
                           :: walk block
                  val name = concat ["cluster_", fname]
              in  << (dot, SUBGRAPH (SOME name, stmts))
              end
            val dot = empty (true, "control-flow")
            val dot = LCPS.FunTbl.foldi addFunCluster dot funtbl
            val dot = << (dot, NODE (nodeId start,
              [("label", "START" ^ ann start), ("shape", "box"),
               ("color", "red")]))
            val dot = NodeTbl.foldi addEdges dot succ
        in  dump dot
        end
      fun dumpDot graph = dumpDot' (graph, fn _ => "")
    end
  end

  structure LoopNestingTree :> sig
    datatype node_type = NonHeader | Self | Reducible | Irreducible
    type loop_info = { nestingDepth: int, header: Graph.node, ty: node_type }
    type looptbl = loop_info Graph.NodeTbl.hash_table

    val build : Graph.t -> looptbl
  end = struct
    type number_tbl = int Graph.NodeTbl.hash_table
    type node_tbl   = Graph.node Array.array
    type last_tbl   = int Array.array

    structure NodeTbl = Graph.NodeTbl

    fun getPreorderNumbers (graph: Graph.t) : number_tbl * node_tbl * last_tbl =
      let val counter = ref 0
          fun incr (r as ref n) = r := n + 1

          val start   = Graph.root graph
          val nodeTbl = Array.array (Graph.numNodes graph, start)
          val lastTbl = Array.array (Graph.numNodes graph, ~1)
          val numberTbl = NodeTbl.mkTable (Graph.numNodes graph, Fail "number")

          fun dfs node =
            let val curr = !counter before incr counter
                val () = NodeTbl.insert numberTbl (node, curr)
                val () = Array.update (nodeTbl, curr, node)
                val () = app (fn succ =>
                  if NodeTbl.inDomain numberTbl succ then () else dfs succ)
                  (Graph.succ (graph, node))
                val last = !counter - 1
            in  Array.update (lastTbl, curr, last)
            end

          val () = dfs start
          val () = if !counter <> (Graph.numNodes graph) then
                     raise Fail "???"
                   else ()

      in  (numberTbl, nodeTbl, lastTbl)
      end

    fun mkUnionFind sz = Array.tabulate (sz, fn i => i)

    fun find trees =
      let fun loop u =
            let val parent = Array.sub (trees, u)
            in  if u = parent then
                  u
                else
                  let val root = loop parent (* path compression *)
                  in  Array.update (trees, u, root); root
                  end
            end
      in  loop
      end

    fun union trees (t1, t2) =
      let val r1 = find trees t1
          val r2 = find trees t2
      in  case Int.compare (r1, r2)
            of EQUAL   => ()
             | LESS    => Array.update (trees, r2, r1)
             | GREATER => Array.update (trees, r1, r2)
      end

    datatype node_type = NonHeader | Self | Reducible | Irreducible

    fun nodeTyToString NonHeader = "nonheader"
      | nodeTyToString Self = "self"
      | nodeTyToString Reducible = "reducible"
      | nodeTyToString Irreducible = "irreducible"

    structure IntSet = IntRedBlackSet

    (* Paul Havlak. "Nesting of Reducible and Irreducible Loops." TOPLAS'97 *)
    fun analyzeLoops (graph, numTbl, lastTbl) =
      let val numNodes     = Graph.numNodes graph
          val backPreds    = Array.tabulate (numNodes, fn _ => [])
          val nonBackPreds = Array.tabulate (numNodes, fn _ => [])
          val header       = Array.tabulate (numNodes, fn _ => 0) (* start *)
          val tyTbl        = Array.tabulate (numNodes, fn _ => NonHeader)

          fun numberOf node = NodeTbl.lookup numTbl node
          fun isAncestor (w, v) = w <= v andalso v <= Array.sub (lastTbl, w)

          fun partitionPred (node, preds) =
            let val w = numberOf node
                val vs = map numberOf preds
                (* For an edge (v -> w), if w is an ancestor of v, then v -> w
                 * is a back edge. *)
                val (back, nonBack) =
                  List.partition (fn v => isAncestor (w, v)) vs
            in  Array.update (backPreds, w, back);
                Array.update (nonBackPreds, w, nonBack)
            end
          val () = Graph.appPred (graph, partitionPred)

          (* Initialize the Union-Find data structure *)
          val trees = mkUnionFind numNodes
          val find  = find trees
          val union = union trees

          fun prependNonBackPreds (w, y) =
            let val nonBack = Array.sub (nonBackPreds, w)
            in  Array.update (nonBackPreds, w, y :: nonBack)
            end

          (* Main analysis loop *)
          fun loop 0 = ()
            | loop w =
              let (* Get all back-edge predecessors *)
                  val (preds, ty) =
                    foldl (fn (v, (preds, hasSelf)) =>
                      if v = w then
                        (preds, Self)
                      else
                        (IntSet.add (preds, find v), Reducible)
                    ) (IntSet.empty, NonHeader) (Array.sub (backPreds, w))

                  (* Chase upwards for all non-back-edge predecessors of the
                   * back-edge predecessors of w. This step finds the nodes in
                   * the body of the loop. *)
                  fun chaseUpward ([], preds, ty) = (preds, ty)
                    | chaseUpward (x :: wl, preds, ty) =
                        let fun chase (y, (wl, preds, ty)) =
                              let val y' = find y
                              in  if not (isAncestor (w, y')) then
                                    (* if w is not an ancestor of y', there is
                                     * another path into w's loop that avoids w.
                                     * This loop is irreducible. *)
                                    (prependNonBackPreds (w, y');
                                     (wl, preds, Irreducible))
                                  else if (not (IntSet.member (preds, y')))
                                          andalso (y' <> w) then
                                    (y' :: wl, IntSet.add (preds, y'), ty)
                                  else
                                    (wl, preds, ty)
                              end
                            val (wl, preds, ty) =
                              foldl chase (wl, preds, ty)
                                          (Array.sub (nonBackPreds, x))
                        in  chaseUpward (wl, preds, ty)
                        end

                  val (preds, ty) =
                    chaseUpward (IntSet.listItems preds, preds, ty)

                  val () = IntSet.app (fn x =>
                    (Array.update (header, x, w); union (x, w))
                  ) preds

                  val () = Array.update (tyTbl, w, ty)

                  (* val () = app print [ *)
                  (*   "Processed ", Int.toString w, ": ", *)
                  (*   "type=", nodeTyToString ty, " ", *)
                  (*   "preds=[", String.concatWithMap "," Int.toString *)
                  (*   (IntSet.listItems preds), "] "] *)

                  (* val () = app print [ *)
                  (*   "header=", String.concatWithMap "," Int.toString *)
                  (*   (Array.toList header), "\n"] *)

              in  loop (w - 1)
              end

          val () = loop (numNodes - 1)
      in  (header, tyTbl)
      end

    type loop_info = { nestingDepth: int, header: Graph.node, ty: node_type }
    type looptbl = loop_info Graph.NodeTbl.hash_table

    fun convertTree (nodeTbl, header, tyTbl): loop_info NodeTbl.hash_table =
      let val numNodes = Array.length nodeTbl
          val loopTbl  = NodeTbl.mkTable (numNodes, Fail "loop table")
          fun iter v =
            if v >= numNodes then
              ()
            else
              let val hdr     = Array.sub (header, v)
                  val hdrNode = Array.sub (nodeTbl, hdr)
                  val ty      = Array.sub (tyTbl, v)
                  val { nestingDepth, ... } = (NodeTbl.lookup loopTbl hdrNode)
                  handle e => raise e
                  val info =
                    { nestingDepth=nestingDepth + 1, header=hdrNode, ty=ty }
                  val node = Array.sub (nodeTbl, v)
              in  NodeTbl.insert loopTbl (node, info);
                  iter (v + 1)
              end
          val start = Array.sub (nodeTbl, 0)
          val () = NodeTbl.insert loopTbl (start,
            { nestingDepth=0, header=start, ty=NonHeader })
          val () = iter 1
      in  loopTbl
      end

    fun annotateWithTbl (numTbl, loopTbl : loop_info NodeTbl.hash_table) node =
      let val number = NodeTbl.lookup numTbl node
          val {nestingDepth, header, ty} = (NodeTbl.lookup loopTbl node)
          handle e => (print (Graph.nodeToString node); raise e)
          val hdrnum = NodeTbl.lookup numTbl header
      in  concat ["(", Int.toString number, ",", Int.toString hdrnum, ",",
                  Int.toString nestingDepth, ",", nodeTyToString ty, ")"]
      end


    fun build (graph: Graph.t) =
      let val (numTbl, nodeTbl, lastTbl) = getPreorderNumbers graph
          val (header, tyTbl) = analyzeLoops (graph, numTbl, lastTbl)
          val loopTbl = convertTree (nodeTbl, header, tyTbl)
          (* val () = Graph.dumpDot' (graph, annotateWithTbl (numTbl, loopTbl)) *)
      in  loopTbl
      end
  end

  type looptbl = LoopNestingTree.loop_info Graph.NodeTbl.hash_table

  (* TODO: move this structure to another file *)
  structure SharingAnalysis :> sig
    type pack
    val preference : LCPS.function * S.t * funtbl * looptbl
                  -> pack Group.Tbl.hash_table
  end = struct
    structure PackID = IdentifierFn( )

    datatype pack = Pack of {
      packs: PackID.Set.set,
      loose: LV.Set.set,
      fv: LV.Set.set (* Invariant: disjointU (packs, loose) = fv *)
    }

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
            in  List.exists (fn f => LV.same (#2 f, #2 defsite)) fs
            end

          val packTbl = PackID.Tbl.mkTable (S.numFuns syn, Fail "pack table")
          val insertPack = PackID.Tbl.insert packTbl
          val lookupPack = PackID.Tbl.lookup packTbl
          val findPack = PackID.Tbl.find packTbl

          val grpTbl = Group.Tbl.mkTable (S.numFuns syn, Fail "grp table")
          val insertGroup = Group.Tbl.insert grpTbl
          val lookupGroup = Group.Tbl.lookup grpTbl

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

                val () =
                  let val name = String.concatWithMap "," (LV.lvarName o #2)
                                                       functions
                  in  app print ["IN FUNCTIONS ", name, "\n"]
                  end

                (* See if we can throw any of the lower-level packs up since if
                 * not we are responsible for allocating the pack. *)
                val (ineligibles, candidates) =
                  List.partition (fn (_, Pack { fv, ... }) =>
                    LV.Set.exists (introducedAt functions) fv
                  ) lowerLevelPacks

                val () =
                  app print [
                  "candidates=[", String.concatWithMap ", "
                  (packToString o #2) candidates, "]\n",
                  "ineligibles=[", String.concatWithMap ", "
                  (packToString o #2) ineligibles, "]\n"]


                val (usedFV, unusedFV) = LV.Set.partition (isUsed functions) fv

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
                  in  pick (candidates, [], unusedFV)
                  end

                (* These are the free variables that the packs have not
                 * accounted for. *)
                val loose =
                  let val fv = LV.Set.union (usedFV, remainingFV)
                      val fv = LV.Set.listItems fv
                  in  map (fn v => (v, defDepth v)) fv
                  end

                val currDepth = S.depthOf syn (List.hd functions)

                val (packs, loose) =
                  let fun cutoff (_, depth) = currDepth - depth >= 3
                      val (far, near) = List.partition cutoff loose
                  in  if List.length far >= 3 then
                        let val loose = LV.Set.fromList (map #1 far)
                            val newpack =
                              mkPack functions {
                                  packs=PackID.Set.empty,
                                  loose=loose,
                                  fv=loose
                                }
                        in  (newpack :: packs, near)
                        end
                      else
                        (packs, loose)
                  end
                val result = Pack {
                    packs=PackID.Set.fromList (map #1 packs),
                    loose=LV.Set.fromList (map #1 loose),
                    fv=fv
                  }
                val () = print "\n\n"
            in  insertGroup (grp, result); result
            end
          val () =
            let val fixes = sortFixes [lookupBlock cps]
                val packs = map ask fixes
            in  ()
            end

          val () = Group.Tbl.appi (fn (g, pack) =>
            let val fs = S.groupFun syn g
                val name = String.concatWithMap "," (LV.lvarName o #2)
                                                    (Vector.toList fs)
            in  app print [name, " --> ", packToString pack, "\n"]
            end) grpTbl
          val () = print "==============\n"
          val () = PackID.Tbl.appi (fn (p, pack) =>
            app print [PackID.toString p, " --> ", packToString pack, "\n"]
          ) packTbl
      in  grpTbl
      end

      (* Generate a dot file *)
  end

  fun analyze (cps, syn, flow: FlowCFA.result) =
    let val funtbl = Summary.analyze syn
        val graph  = Graph.build (funtbl, syn, flow)
        val loopTbl = LoopNestingTree.build graph
        val _ = SharingAnalysis.preference (cps, syn, funtbl, loopTbl)
        (* val () = Graph.dumpDot graph *)
    in  ()
    end
end
