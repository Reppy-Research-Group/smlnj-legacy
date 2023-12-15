local
	fun f1 () = print "a"
	fun f2 () = print "b"

	val r = ref f1
in
	val _ = (r := f2; !r ())
end
