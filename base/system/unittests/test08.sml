structure A :> sig val evens : int list -> int list end = struct
	fun filter p [] = []
		| filter p (x :: xs) = if p x then x :: xs else xs

	fun isEven 0 = true
		| isEven 1 = false
		| isEven n = not (isOdd (n - 1))
	and isOdd 0 = false
		| isOdd 1 = true
		| isOdd n = not (isEven (n - 1))

	fun evens xs = filter isEven xs
end
