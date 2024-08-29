structure A :> sig type t val run : int -> int end = struct
	datatype t = A of int -> int
						 | B
						 | C

	fun nth ([], _) = raise Subscript
		| nth (x :: xs, 0) = x
		| nth (x :: xs, n) = nth (xs, n - 1)

	val unused = nth ([B, A (fn x => x + 42), C], 1)

	fun run' (A f) (x: int) = f x
		| run' B x = 30
		| run' C x = 40

	val run = run' unused
end
