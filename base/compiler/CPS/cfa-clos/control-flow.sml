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
  withtype fix = LCPS.label * LCPS.function list

  type funtbl = block LCPS.FunTbl.hash_table

  fun terminatorName (Return _) = "return"
    | terminatorName (Call _) = "call"
    | terminatorName (Raise _) = "raise"
    | terminatorName (Branch _) = "branch"
    | terminatorName (Switch _) = "switch"

  (* number: block -> int
   * node  : int -> block
   * last  : int -> int
   * pred  : int -> int
   * succ  : int -> int
   * entry : function -> block      <--- implied
   * owner : block    -> function   <--- add??
   *
   * succ_kind : Goto, Approximate, Fake
   * pred_kind : Goto, Approximate, Fake
   *)

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
                      fix=(l, functions)::fix,
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

    type t
    val build : funtbl * S.t * FlowCFA.result -> t

    val root : t -> node
    val succ : t * node -> block list
    val pred : t * node -> node list

    val dumpDot : t -> unit
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
    fun succ (Graph { succ=succTbl, ... }, n) =
      destsOfEdge (NodeTbl.lookup succTbl n)
    fun pred (Graph { pred=predTbl, ... }, n) =
      NodeTbl.lookup predTbl n

    local open DotLanguage in
      fun dumpDot (Graph { start, funtbl, succ, pred }) =
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
                                  [("style", "dashed"), ("color", "red")])) dests
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
              let fun blocknode (Block {label, term, ...}) : stmt =
                    NODE (LV.lvarName label,
                          [("label", terminatorName term), ("shape", "box")])
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
              [("label", "START"), ("shape", "box"), ("color", "red")]))
            val dot = NodeTbl.foldi addEdges dot succ
        in  dump dot
        end
    end
  end


  (* TODO: put this in syntactic analysis *)
  fun immediateCallSites ((_, _, _, _, body): LCPS.function)
    : (LCPS.label * LCPS.value * LCPS.value list) list =
    let fun walk (LCPS.FIX (_, _, exp)) = walk exp
          | walk (LCPS.APP app) = [app]
          | walk (LCPS.SWITCH (_, _, _, exps)) = List.concatMap walk exps
          | walk (LCPS.BRANCH (_, _, _, _, exp1, exp2)) = walk exp1 @ walk exp2
          | walk ( LCPS.RECORD (_, _, _, _, exp)
                 | LCPS.SELECT (_, _, _, _, _, exp)
                 | LCPS.OFFSET (_, _, _, _, exp)
                 | LCPS.SETTER (_, _, _, exp)
                 | LCPS.LOOKER (_, _, _, _, _, exp)
                 | LCPS.ARITH  (_, _, _, _, _, exp)
                 | LCPS.PURE   (_, _, _, _, _, exp)
                 | LCPS.RCC    (_, _, _, _, _, _, exp)) = walk exp
    in  walk body
    end

  fun analyze (cps, syn, flow: FlowCFA.result) =
    let val funtbl = Summary.analyze syn
        val graph  = Graph.build (funtbl, syn, flow)
        val () = Graph.dumpDot graph
    in  ()
    end
end
