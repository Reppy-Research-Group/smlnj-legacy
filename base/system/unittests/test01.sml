local
	fun gen (a, b) =
		let
			fun c1 () = print "a"
			fun c2 () = print "b"
		in
			(a + b; c1) handle Overflow => c2
		end
in
	fun f (a, b) = gen (a, b) ()
end
