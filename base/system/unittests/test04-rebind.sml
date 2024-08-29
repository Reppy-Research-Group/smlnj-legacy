structure A :> sig val run : int -> int list end = struct
	fun big (base, n) = if n < 1 then [base] else n :: big (base, n - 1)

	fun run base = big (base, 10000)
end
