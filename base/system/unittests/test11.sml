fun f (x, y) k =
	let 
    fun mk (0, acc) = acc
      | mk (n, acc) = (fn x => x + 1) o acc
	    val g = mk (x, k)
  in  g y
  end
