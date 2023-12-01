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

  fun build {cps: LCPS.function, lookup, filter, escapingLambdas} =
    let
      type call_data = {
        callees: LCPS.function vector option,
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
          fun exp (cexp as LCPS.APP (_, CPS.VAR f, args)) =
               let
                 val callees = Option.map Vector.fromList (filter (lookup f))
                 val callData = { callees=callees, enclosing=function }
                 val () = LCPS.Tbl.insert appTbl (cexp, callData)
                 val () = Option.app (Vector.app (insertCallsite cexp)) callees
                 val () = insertTerminator function cexp
               in
                 ()
               end
            | exp (LCPS.APP _) = raise Fail "app not var impossible"
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


  type tbl = VSet.set VTbl.hash_table
  type t = tbl * tbl

  exception LookUp

  fun new () = (VTbl.mkTable (4096, LookUp), VTbl.mkTable (4096, LookUp))

  fun insert map (k, v) =
    let val set' = case VTbl.find map k
                     of SOME set => VSet.add (set, v)
                      | NONE => VSet.singleton v
    in  VTbl.insert map (k, set')
    end

  fun member map (f, g) =
    case VTbl.find map f
      of SOME set => VSet.member (set, g)
       | NONE => false

  fun add ((caller, callee), f, g) =
    (insert caller (g, f); (* f is a caller of g *)
     insert callee (f, g)) (* g is a callee of f *)

  fun callers ((caller, _), f) =
    case VTbl.find caller f
      of SOME set => VSet.toList set
       | NONE => []

  fun callees ((_, callee), f) =
    case VTbl.find callee f
      of SOME set => VSet.toList set
       | NONE => []

  fun isCaller (caller, _) = member caller
  fun isCallee (_, callee) = member callee

end
