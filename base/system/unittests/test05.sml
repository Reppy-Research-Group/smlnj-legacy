structure Main :> sig
  type tree
  val x : tree
  val sum : tree -> int
end = struct
  datatype tree = NODE of tree * tree
                | LEAF of int

  val x = NODE (NODE (LEAF 1, LEAF 2), NODE (LEAF 3, LEAF 4))

  fun sum (NODE (left, right)) = sum left + sum right
    | sum (LEAF x) = x
end
