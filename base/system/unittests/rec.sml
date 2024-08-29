fun apply (f, x) = f x;


fun even 0 = true
	| even n = apply (odd, n - 1)
and odd 0 = false
	| odd n = apply (even, n - 1)
