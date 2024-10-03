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
    | Branch of CPS.P.branch * CPS.value list * block * block * prob
    | Switch of (block * prob) list
  withtype fix = LCPS.label * LCPS.function list
       and block = { term: terminator, fix: fix list }

  type funtbl = block LCPS.FunTbl.hash_table

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

    fun predict (lookup, test, args, block1: block, block2: block): prob =
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
          val {term=term1, ...} = block1
          val {term=term2, ...} = block2

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
                | (Return _, _) => SOME notRH
                | (_, Return _) => SOME RH
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
      in  case foldl combine NONE heuristics
            of NONE => Prob.prob (1, 2)
             | SOME prob => prob
      end

    fun calculate (f: LCPS.function, syn: S.t): block =
      let val info = LV.Tbl.mkTable (32, Fail "info table")
          val insertInfo = LV.Tbl.insert info
          val lookupInfo = LV.Tbl.find info
          val typeof = S.typeof syn
          fun walk (LCPS.APP (_, CPS.VAR v, args)) =
                let val term =
                      (case typeof v
                         of CPS.CNTt => Return (v, args)
                          | _ => (case lookupInfo v
                                    of SOME Handler => Raise (v, args)
                                     | _ => Call (v, args)))
                in  { term=term, fix=[] }
                end
            | walk (LCPS.APP (_, _, _)) = raise Fail "App non arg"
            | walk (LCPS.FIX (label, functions, exp)) =
                let val { term, fix } = walk exp
                in  { term=term, fix=(label, functions)::fix }
                end
            | walk (LCPS.BRANCH (_, branch, args, _, exp1, exp2)) =
                let val blk1 = walk exp1
                    val blk2 = walk exp2
                    val prob = predict (lookupInfo, branch, args, blk1, blk2)
                in  { term=Branch (branch, args, blk1, blk2, prob), fix=[] }
                end
            | walk (LCPS.SWITCH (_, _, _, exps)) =
                let val length = List.length exps
                    (* TODO: multi-arm branch prediction?
                     *
                     * The problem with SWITCH in the CPS IR is that there is no
                     * information on the SWITCH argument --- it is just an
                     * integer. The only heuristics that could apply is RH, and
                     * I'm not sure how useful it is. *)
                    val prob   = Prob.prob (1, length)
                    val blocks = map (fn e => (walk e, prob)) exps
                in  { term=Switch blocks, fix=[] }
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

  datatype node = Start
                | Function of LCPS.function
                | End

  fun nodeToNode Start = ("start", [("color", "red")])
    | nodeToNode (Function f) = (LV.lvarName (#2 f), [])
    | nodeToNode End = ("end", [("color", "blue")])

  fun analyze (cps, syn, {lookup, flow}: FlowCFA.result) =
    let fun escapes f = #escape (flow f)
        val escaping =
          S.foldF syn (fn (f, acc) => if escapes f then f :: acc else acc) [cps]

        fun functionOfValue (CPS.VAR v) =
              (case lookup v
                 of NONE => []
                  | SOME { unknown=true, ... } => []
                  | SOME { known, ... } => known)
          | functionOfValue _ = []

        fun successor Start = map (fn f => (Function f, [])) escaping
          | successor (Function f) =
              let val calls = immediateCallSites f
                  fun convert (_, CPS.VAR f, args) =
                    (case lookup f
                       of NONE => []
                        | SOME { unknown=true, ... } =>
                            (* If f is calling an unknown function with some
                             * function/continuation as arguments, the assumption
                             * is that the unknown function will call the
                             * functions. *)
                            let val fake = List.concatMap functionOfValue args
                            in  map (fn f => (Function f, [("color", "gray")]))
                                    fake
                            end
                        | SOME { known, ... } =>
                            map (fn f => (Function f, [])) known)
                    | convert _ = []
              in  List.concatMap convert calls
              end
          | successor End = []

        val graph = DotLanguage.fromGraph nodeToNode
                      { roots=map Function escaping, follow=successor }
        val () = DotLanguage.dump graph
    in  ()
    end
end
