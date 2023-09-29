structure CallGraph :> CALL_GRAPH = struct

  structure VTbl = LambdaVar.Tbl
  structure VSet = LambdaVar.Set

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
