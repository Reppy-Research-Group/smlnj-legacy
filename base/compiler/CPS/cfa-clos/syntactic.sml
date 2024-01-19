structure SyntacticInformation :> sig
  type t = {
    freevars : LCPS.function -> LCPS.lvar list,
    callsites : LCPS.function -> LCPS.cexp list,
    enclosing : LCPS.cexp -> LCPS.function,
    usesites : LCPS.lvar -> LCPS.cexp list
  }

  val calculate : LCPS.function -> t
end = struct
  type fun_info = {
    freevars: LCPS.lvar list,
    callsites: LCPS.cexp list
  }

  type exp_info = {
    enclosing: LCPS.function
  }

  type var_info = {
    usesites : LCPS.cexp list
  }

  structure FunTbl = HashTableFn(struct
    type hash_key = LCPS.function
    val nameOf = #2 : hash_key -> LambdaVar.lvar
    val hashVal = (Word.fromInt o LambdaVar.toId o nameOf)
    fun sameKey (f1, f2) = LambdaVar.same (nameOf f1, nameOf f2)
  end)

  structure VarTbl = LambdaVar.Tbl
  exception SyntacticInfo
  fun calculate (funkind, name, formals, tys, body) =
    let
      val expTable : exp_info LCPS.Tbl.hash_table =
        LCPS.Tbl.mkTable (2048, SyntaticInfo)
      val funTable : fun_info FunTbl.hash_table =
        FunTbl.mkTable (2048, SyntaticInfo)
      val varTable : var_info VarTbl.hash_table =
        VarTbl.mkTable (2048, SyntaticInfo)
    in
      raise Fail "unimp"
    end
end
