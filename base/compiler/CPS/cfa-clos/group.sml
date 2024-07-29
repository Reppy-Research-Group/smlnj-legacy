structure Group :> sig
  (* a group is represented by the label of the letfun *)
  type t

  val fromExp : LabelledCPS.cexp -> t
  val wrap : LabelledCPS.label -> t
  val unwrap : t -> LabelledCPS.label
  val toString : t -> string

  structure Map : ORD_MAP where type Key.ord_key = t
  structure Set : ORD_SET where type Key.ord_key = t
  structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t
  structure MonoSet : MONO_HASH_SET where type Key.hash_key = t
end = struct
  structure LV = LambdaVar

  type t = LabelledCPS.label

  fun fromExp (LabelledCPS.FIX (label, _, _)) = label
    | fromExp _ = raise Fail "Group: Not a fix"

  fun wrap x = x
  fun unwrap x = x
  val toString = LV.lvarName

  structure Map = LV.Map
  structure Set = LV.Set
  structure Tbl = LV.Tbl
  structure MonoSet = HashSetFn(LV.Tbl.Key)

end
