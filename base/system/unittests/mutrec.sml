datatype 'a result = Base
									 | Recur of int -> 'a result
fun even 0 = Base
	| even n = Recur odd
and odd 0 = Base
	| odd n = Recur even
