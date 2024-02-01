structure LabelledCPS :> sig
  type label = LambdaVar.lvar

  type record_kind = CPS.record_kind
  type pkind       = CPS.pkind
  type intty       = CPS.intty
  type cty         = CPS.cty
  type lvar        = CPS.lvar
  type value       = CPS.value
  type accesspath  = CPS.accesspath
  type fun_kind    = CPS.fun_kind

  datatype cexp
    = RECORD of label * record_kind * (lvar * value * accesspath) list * lvar * cexp
    | SELECT of label * int * value * lvar * cty * cexp
    | OFFSET of label * int * value * lvar * cexp
    | APP of label * value * value list
    | FIX of label * function list * cexp
    | SWITCH of label * value * lvar * cexp list
    | BRANCH of label * CPS.P.branch * value list * lvar * cexp * cexp
    | SETTER of label * CPS.P.setter * value list * cexp
    | LOOKER of label * CPS.P.looker * value list * lvar * cty * cexp
    | ARITH of label * CPS.P.arith * value list * lvar * cty * cexp
    | PURE of label * CPS.P.pure * value list * lvar * cty * cexp
    | RCC of label * bool * string * CTypes.c_proto * value list *
             (lvar * cty) list * cexp
    withtype function = fun_kind * lvar * lvar list * cty list * cexp

  val nameOfF : function -> lvar

  val label   : CPS.cexp -> cexp
  val unlabel : cexp -> CPS.cexp

  val labelOf : cexp -> label
  val same : cexp * cexp -> bool

  val labelF   : CPS.function -> function
  val unlabelF : function -> CPS.function

  structure Map : ORD_MAP where type Key.ord_key = cexp
  structure Set : ORD_SET where type Key.ord_key = cexp
  structure Tbl : MONO_HASH_TABLE where type Key.hash_key = cexp

  structure FunMap : ORD_MAP where type Key.ord_key = function
  structure FunSet : ORD_SET where type Key.ord_key = function
  structure FunMonoSet : MONO_HASH_SET where type Key.hash_key = function
  structure FunTbl : MONO_HASH_TABLE where type Key.hash_key = function
end = struct
  type label = LambdaVar.lvar

  type record_kind = CPS.record_kind
  type pkind       = CPS.pkind
  type intty       = CPS.intty
  type cty         = CPS.cty
  type lvar        = CPS.lvar
  type value       = CPS.value
  type accesspath  = CPS.accesspath
  type fun_kind    = CPS.fun_kind

  datatype cexp
    = RECORD of label * record_kind * (lvar * value * accesspath) list * lvar * cexp
    | SELECT of label * int * value * lvar * cty * cexp
    | OFFSET of label * int * value * lvar * cexp
    | APP of label * value * value list
    | FIX of label * function list * cexp
    | SWITCH of label * value * lvar * cexp list
    | BRANCH of label * CPS.P.branch * value list * lvar * cexp * cexp
    | SETTER of label * CPS.P.setter * value list * cexp
    | LOOKER of label * CPS.P.looker * value list * lvar * cty * cexp
    | ARITH of label * CPS.P.arith * value list * lvar * cty * cexp
    | PURE of label * CPS.P.pure * value list * lvar * cty * cexp
    | RCC of label * bool * string * CTypes.c_proto * value list *
             (lvar * cty) list * cexp
    withtype function = fun_kind * lvar * lvar list * cty list * cexp

  val mkLabel = LambdaVar.mkLvar

  fun nameValueList (values : (value * accesspath) list) =
    map (fn (v, p) => (LambdaVar.mkLvar (), v, p)) values

  fun unnameValueList (values : (lvar * value * accesspath) list) =
    map (fn (_, v, p) => (v, p)) values

  fun label (CPS.RECORD (kind, values, x, cexp)) =
        RECORD (mkLabel (), kind, nameValueList values, x, label cexp)
    | label (CPS.SELECT (n, v, x, cty, cexp)) =
        SELECT (mkLabel (), n, v, x, cty, label cexp)
    | label (CPS.OFFSET (n, v, x, cexp)) =
        OFFSET (mkLabel (), n, v, x, label cexp)
    | label (CPS.APP (f, args)) =
        APP (mkLabel (), f, args)
    | label (CPS.FIX (bindings, body)) =
        FIX (mkLabel (), map labelF bindings, label body)
    | label (CPS.SWITCH (v, id, branches)) =
        SWITCH (mkLabel (), v, id, map label branches)
    | label (CPS.BRANCH (br, args, id, trueExp, falseExp)) =
        BRANCH (mkLabel (), br, args, id, label trueExp, label falseExp)
    | label (CPS.SETTER (oper, args, body)) =
        SETTER (mkLabel (), oper, args, label body)
    | label (CPS.LOOKER (oper, args, x, cty, body)) =
        LOOKER (mkLabel (), oper, args, x, cty, label body)
    | label (CPS.ARITH (oper, args, x, cty, body)) =
        ARITH (mkLabel (), oper, args, x, cty, label body)
    | label (CPS.PURE (oper, args, x, cty, body)) =
        PURE (mkLabel (), oper, args, x, cty, label body)
    | label (CPS.RCC (b, name, cType, values, vars, body)) =
        RCC (mkLabel (), b, name, cType, values, vars, label body)
  and labelF (funkind, name, formals, types, body) =
        (funkind, name, formals, types, label body)

  fun labelOf (RECORD data) = #1 data
    | labelOf (SELECT data) = #1 data
    | labelOf (OFFSET data) = #1 data
    | labelOf (APP data) = #1 data
    | labelOf (FIX data) = #1 data
    | labelOf (SWITCH data) = #1 data
    | labelOf (BRANCH data) = #1 data
    | labelOf (SETTER data) = #1 data
    | labelOf (LOOKER data) = #1 data
    | labelOf (ARITH data) = #1 data
    | labelOf (PURE data) = #1 data
    | labelOf (RCC data) = #1 data

  fun nameOfF ((_, name, _, _, _): function) = name

  fun unlabel (RECORD (_, kind, values, v, cexp)) =
        CPS.RECORD (kind, unnameValueList values, v, unlabel cexp)
    | unlabel (SELECT (_, n, v, x, cty, cexp)) =
        CPS.SELECT (n, v, x, cty, unlabel cexp)
    | unlabel (OFFSET (_, n, v, x, cexp)) =
        CPS.OFFSET (n, v, x, unlabel cexp)
    | unlabel (APP (_, f, args)) =
        CPS.APP (f, args)
    | unlabel (FIX (_, bindings, body)) =
        CPS.FIX (map unlabelF bindings, unlabel body)
    | unlabel (SWITCH (_, v, id, branches)) =
        CPS.SWITCH (v, id, map unlabel branches)
    | unlabel (BRANCH (_, br, args, id, trueExp, falseExp)) =
        CPS.BRANCH (br, args, id, unlabel trueExp, unlabel falseExp)
    | unlabel (SETTER (_, oper, args, body)) =
        CPS.SETTER (oper, args, unlabel body)
    | unlabel (LOOKER (_, oper, args, x, cty, body)) =
        CPS.LOOKER (oper, args, x, cty, unlabel body)
    | unlabel (ARITH (_, oper, args, x, cty, body)) =
        CPS.ARITH (oper, args, x, cty, unlabel body)
    | unlabel (PURE (_, oper, args, x, cty, body)) =
        CPS.PURE (oper, args, x, cty, unlabel body)
    | unlabel (RCC (_, b, name, ctype, values, vars, body)) =
        CPS.RCC (b, name, ctype, values, vars, unlabel body)
  and unlabelF (funkind, name, formals, types, body) =
        (funkind, name, formals, types, unlabel body)

  fun same (c1, c2) = LambdaVar.same (labelOf c1, labelOf c2)

  structure OrdKey : ORD_KEY = struct
    type ord_key = cexp
    fun compare (c1, c2) = LambdaVar.compare (labelOf c1, labelOf c2)
  end

  structure HashKey : HASH_KEY = struct
    type hash_key = cexp
    val hashVal = Word.fromInt o LambdaVar.toId o labelOf
    val sameKey = same
  end

  structure Map = RedBlackMapFn(OrdKey)
  structure Set = RedBlackSetFn(OrdKey)
  structure Tbl = HashTableFn(HashKey)

  structure FunOrdKey : ORD_KEY = struct
    type ord_key = function
    fun compare (f1, f2) = LambdaVar.compare (nameOfF f1, nameOfF f2)
  end
  structure FunHashKey : HASH_KEY = struct
    type hash_key = function
    val hashVal = Word.fromInt o LambdaVar.toId o nameOfF
    fun sameKey (f1, f2) = LambdaVar.same (nameOfF f1, nameOfF f2)
  end

  structure FunMap = RedBlackMapFn(FunOrdKey)
  structure FunSet = RedBlackSetFn(FunOrdKey)
  structure FunMonoSet = HashSetFn(FunHashKey)
  structure FunTbl = HashTableFn(FunHashKey)
end
