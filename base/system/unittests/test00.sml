structure A :> sig val ok : bool * bool end = struct
	fun id x = x

	fun check () =
		let val t = id true
				val t2 = id false
		in  (t, t2)
		end

	val ok = check ()
end
