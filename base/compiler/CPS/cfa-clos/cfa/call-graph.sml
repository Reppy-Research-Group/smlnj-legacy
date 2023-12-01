signature CALL_GRAPH = sig
  type t

  val build : {
    cps: LabelledCPS.function,
    lookup : CPS.lvar -> 'value option,
    filter :'value -> LabelledCPS.function list option,
    escapingLambdas: LabelledCPS.function vector
  } -> t

  datatype component = SINGLE of LabelledCPS.function
                     | GROUP of LabelledCPS.function list
  val scc : t -> component list
end

structure CallGraph :> CALL_GRAPH = struct
  structure VTbl = LambdaVar.Tbl
  structure VSet = LambdaVar.Set
  structure LCPS = LabelledCPS

  datatype t = T of {
    getCallees : LCPS.cexp -> LCPS.function vector option,
    getCallsites: LCPS.function -> LCPS.cexp vector,
    getEnclosingLam : LCPS.cexp -> LCPS.function,
    getTerminators : LCPS.function -> LCPS.cexp vector,
    escapingLam : LCPS.function vector,
    allLambdas  : LCPS.function vector
  }

  structure FunTbl = HashTableFn(struct
    type hash_key = LCPS.function
    val nameOf = #2 : hash_key -> LambdaVar.lvar
    val hashVal = (Word.fromInt o LambdaVar.toId o nameOf)
    fun sameKey (f1, f2) = LambdaVar.same (nameOf f1, nameOf f2)
  end)

  fun build {cps, lookup, filter, escapingLambdas} =
    let
      type call_data = {
        callees: LCPS.function vector option,
        dead: bool,
        enclosing: LCPS.function
      }
      val appTbl = LCPS.Tbl.mkTable (2048, Fail "callee table")
      val _ = appTbl : call_data LCPS.Tbl.hash_table

      type fun_data = { callsites: LCPS.cexp list, terminators: LCPS.cexp list }
      val funTbl = FunTbl.mkTable (2048, Fail "function table")
      val _ = funTbl : fun_data FunTbl.hash_table

      fun insertCallsite site f =
        case FunTbl.find funTbl f
          of SOME { callsites, terminators } =>
               if List.exists (fn s => LCPS.same (site, s)) callsites then
                 ()
               else
                 FunTbl.insert funTbl
                   (f, { callsites=site::callsites, terminators=terminators })
           | NONE =>
               FunTbl.insert funTbl (f, { callsites=[site], terminators=[] })
      fun insertTerminator f cexp =
        case FunTbl.find funTbl f
          of SOME { callsites, terminators } =>
               FunTbl.insert funTbl
                 (f, { callsites=callsites, terminators=cexp::terminators })
           | NONE =>
               FunTbl.insert funTbl (f, { callsites=[], terminators=[cexp] })

      val allLambdas = ref [] : LCPS.function list ref

      fun walkF (function as (_, _, _, _, body)) =
        let
          val () = allLambdas := function :: (!allLambdas)
          fun register f cexp =
            case lookup f
              of NONE =>
                   let
                     val callData = {callees=NONE, dead=true, enclosing=function}
                   in
                     LCPS.Tbl.insert appTbl (cexp, callData);
                     insertTerminator function cexp
                   end
               | SOME values =>
                   let
                     val callees = Option.map Vector.fromList (filter values)
                     val callData =
                       { callees=callees, dead=false, enclosing=function }
                   in
                     LCPS.Tbl.insert appTbl (cexp, callData);
                     Option.app (Vector.app (insertCallsite cexp)) callees;
                     insertTerminator function cexp
                   end

          fun exp (cexp as LCPS.APP (_, CPS.VAR f, args)) = register f cexp
            | exp (LCPS.APP _) = raise Fail "app not var impossible"
            | exp (LCPS.RECORD (_, kind, values, v, cexp)) = exp cexp
            | exp (LCPS.SELECT (_, n, v, x, cty, cexp)) = exp cexp
            | exp (LCPS.OFFSET (_, n, v, x, cexp)) = exp cexp
            | exp (LCPS.FIX (_, bindings, body)) =
                (app walkF bindings; exp body)
            | exp (LCPS.SWITCH (_, v, id, branches)) = app exp branches
            | exp (LCPS.BRANCH (_, br, args, id, trueExp, falseExp)) =
                (exp trueExp; exp falseExp)
            | exp (LCPS.SETTER (_, oper, args, cexp)) = exp cexp
            | exp (LCPS.LOOKER (_, oper, args, x, cty, cexp)) = exp cexp
            | exp (LCPS.ARITH (_, oper, args, x, cty, cexp)) = exp cexp
            | exp (LCPS.PURE (_, oper, args, x, cty, cexp)) = exp cexp
            | exp (LCPS.RCC (_, b, name, ctype, values, vars, cexp)) = exp cexp
                (* FIXME: check RCC case *)
        in
          exp body
        end
      val () = walkF cps
      val funTbl' = FunTbl.map (fn {callsites, terminators} =>
        { callsites=Vector.fromList callsites,
          terminators=Vector.fromList terminators }) funTbl
    in
      T {
        getCallees = #callees o (LCPS.Tbl.lookup appTbl),
        getCallsites = #callsites o (FunTbl.lookup funTbl'),
        getTerminators = #terminators o (FunTbl.lookup funTbl'),
        getEnclosingLam = #enclosing o (LCPS.Tbl.lookup appTbl),
        escapingLam = escapingLambdas,
        allLambdas = Vector.fromList (!allLambdas)
      }
    end

  datatype component = SINGLE of LCPS.function
                     | GROUP of LCPS.function list
  structure SCCSolver = GraphSCCFn(struct
    type ord_key = LCPS.function
    fun compare (f1: ord_key, f2: ord_key) = LambdaVar.compare (#2 f1, #2 f2)
  end)

  fun scc (T {getCallees, getTerminators, escapingLam, ...}) =
    let
      fun concatMapToList f xs =
        Vector.foldr (fn (x, acc) =>
          case f x
            of SOME xs => Vector.foldr (op::) acc xs
             | NONE => acc) [] xs
      val _ = concatMapToList : ('a -> 'b vector option) -> 'a vector -> 'b list
      fun follow func = concatMapToList getCallees (getTerminators func)
      fun convert (SCCSolver.SIMPLE f) = SINGLE f
        | convert (SCCSolver.RECURSIVE fs) = GROUP fs
    in
      map convert (SCCSolver.topOrder'
                     { roots=Vector.toList escapingLam, follow=follow })
    end
end
