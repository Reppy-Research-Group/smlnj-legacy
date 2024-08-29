structure Test :> sig
  val mut : (int -> int) ref
  val mut2 : (int -> int) Array.array
  val run : int -> int
  val run2 : int -> int
  val run3 : int -> int
end = struct
  val mut = ref (fn x => x + 1)
  val mut2 = Array.fromList [fn x => x + 2]
  val mut3 = Array.array (1, fn x => x + 3)
  val () = Array.copy {di=0, src=mut2, dst=mut3}

  fun run x = !mut x
  fun run2 x = Array.sub (mut2, 0) x
  fun run3 x = Array.sub (mut3, 0) x
end;

structure Main :> sig val doit : unit -> unit end = struct
  fun foo x = x + 42
  fun bar x = x * 42
  fun baz x = x mod 42

  val () = Test.mut := foo
  val () = Test.mut := bar
  val () = Test.mut := baz

  fun doit () = print (Int.toString (Test.run 42))
end


