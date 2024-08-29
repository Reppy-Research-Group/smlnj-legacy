structure Main :> sig
  type tree
  val x : tree
  val sum : tree -> (int -> 'a) -> 'a
end = struct
  datatype tree = NODE of tree * tree
                | LEAF of int

  val x = NODE (NODE (LEAF 1, LEAF 2), NODE (LEAF 3, LEAF 4))

  fun sum (NODE (left, right)) k =
		    let fun k' leftSum = sum right (fn rightSum => k (leftSum + rightSum))
			  in  sum left k'
			  end
    | sum (LEAF x) k = k x
end
