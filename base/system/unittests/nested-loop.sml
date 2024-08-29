local
  fun small n = if n < 1 then [] else n :: small (n - 1)
  fun big (n, res) = if n < 1 then res else big (n - 1, small n :: res)
  val N = 100
in

  val result = big (N, [])
  (* val result = big (N, N, N, []) *)
end
