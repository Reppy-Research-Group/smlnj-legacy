structure Main :> sig val doit : unit -> unit end =
struct

  fun map f [] = []
    | map f (a :: x) = f a :: map f x

  fun app f [] = () 
    | app f (a :: x) = (f a; app f x)

  fun mem [] = false
    | mem ([] :: _) = true
    | mem (lst :: lsts) = mem lsts

  fun hd [] = raise Subscript
    | hd (x :: _) = x
  fun tl [] = raise Subscript
    | tl (_ :: xs) = xs

  fun mapAll f [] = []
    | mapAll f xs =
        if mem xs then
          []
        else
          let val heads = map hd xs
              val tails = map tl xs
          in  f heads :: mapAll f tails
          end

  fun foldl f zero [] = zero
    | foldl f zero (x :: xs) = foldl f (f (x, zero)) xs

  fun mapzip f ([], []) = []
    | mapzip f (x::xs, y::ys) = f (x, y) :: mapzip f (xs, ys)
    | mapzip _ _ = raise Subscript

  (* fun matMul (m1 : int list list, m2 : int list list) = *)
  (*   map (fn row => *)
  (*         mapAll *)
  (*           (fn col => foldl (op+) 0 (mapzip (op* ) (row, col))) *)
  (*           m2) *)
  (*       m1 *)

  (* val m1 = [[1, 2], *)
  (*           [3, 4]] *)
  (* val m2 = [[3, 8, 3], *)
  (*           [2, 1, 4]] *)

  fun matMul (m1 : real list list, m2 : real list list) =
    map (fn row =>
          mapAll
            (fn col => foldl (op+) 0.0 (mapzip (op*) (row, col)))
            m2)
        m1

  val m1 = [[1.0, 2.0],
            [3.0, 4.0]]
  val m2 = [[3.0, 8.0, 3.0],
            [2.0, 1.0, 4.0]]
  fun show xs =
    let fun showRow row =
          (print (String.concatWithMap "\t" Real.toString row);
           print "\n")
    in  app showRow xs
    end

  fun doit () =
    let val result = matMul (m1, m2)
    in  show result
    end
end
