structure Main :> sig val main : int list * bool list * string list * int -> int * bool *
string end = struct
  fun nth ([], _) = raise Subscript
    | nth (x :: xs, 0) = x
    | nth (x :: xs, n) = nth (xs, n - 1)

  fun foo (lst, n) =
    nth (lst, n)
    handle Subscript => (print "no"; 0)

  fun bar (lst, n) =
    nth (lst, n)
    handle Subscript => (print "no"; true)

  fun baz (lst, n) =
    nth (lst, n)
    handle Subscript => (print "no"; "hello")

  fun main (lst1, lst2, lst3, n) =
    (foo (lst1, n), bar (lst2, n), baz (lst3, n))
end
