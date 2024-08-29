local
  fun big n = if n < 1 then [0] else n :: big (n - 1)

  fun bigcps (k, n) =
    if n < 1 then k [0]
    else
      let fun k' lst = k (n :: lst)
      in  bigcps (k', n - 1)
      end

  val N = 5000
  fun run f =
    let val onesec = Time.fromSeconds 5
        val endtime =
          (SMLofNJ.Internals.GC.doGC 100000; Time.+ (Time.now(), onesec))
        fun iteration n =
          if Time.>= (Time.now (), endtime) then
            n
          else
            (f N; iteration n + 1)
    in  iteration 0
    end
in
  fun doit () =
    let val () = print "Running big: ... "
        val n  = run big
        val () = print (Int.toString n ^ "\n")
        val () = print "Running bigcps: ... "
        val n' = run (fn n => bigcps (fn x => x, N))
        val () = print (Int.toString n' ^ "\n")
    in  ()
    end
end
