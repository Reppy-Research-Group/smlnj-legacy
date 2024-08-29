structure Main :> sig val doit : int * int -> int end = struct
  val r = ref (SOME 1)

  fun doit (x, y) = (case !r of NONE => x + 1 | SOME _ => y + 42)

end
