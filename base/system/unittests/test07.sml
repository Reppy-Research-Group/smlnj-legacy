datatype 'a tree = Empty | Node of 'a * 'a forest
     and 'a forest = Nil | Cons of 'a tree * 'a forest

fun sizeTree Empty =
      let
        (* prevent inlining *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
      in 
        0
      end
  | sizeTree (Node (_, f)) = 1 + sizeForest f
and sizeForest Nil =
      let
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
        (* val () = print "hello\n" *)
      in 
        0
      end
  | sizeForest (Cons (t, f')) = sizeTree t + sizeForest f'
