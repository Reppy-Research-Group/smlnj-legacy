(* timeit.sml
 *
 * COPYRIGHT (c) 2021 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *)


signature BMARK =
  sig
    val doit : unit -> unit
    val testit : TextIO.outstream -> unit
  end;

structure Timing : sig

    val timeUse : TextIO.outstream * string -> unit

    val timeIt : TextIO.outstream * (unit -> 'a) -> unit

    val time : int * TextIO.outstream * (unit -> 'a) -> unit

  end = struct

    structure TR = Timer
    structure T = Time

    type timing = {usr:T.time, gc:T.time, sys:T.time, real:T.time}

    fun pad (s, n) = StringCvt.padLeft #" " n s

    fun start () = (
          SMLofNJ.Internals.GC.doGC 1000;
          Time.now())

    fun stop startT = Time.-(Time.now(), startT)

    (* convert a time value to a string, padded on the left to 8 characters *)
    fun timeToStr time = pad (Time.toString time, 6)

    fun output (strm, t) = TextIO.output (strm, timeToStr t)

  (* measure the compile time for a file *)
    fun timeUse (outstrm, file) = let
          val t0 = start()
          in
            use file;
            output (outstrm, stop t0)
          end

  (* Time one run of the benchmark *)
    fun timeOne doit = let
          val t0 = start()
          in
            doit();
            stop t0
          end

    fun timeIt (outstrm, doit) = let
            val t = timeOne doit
            in
              TextIO.output1 (outstrm, #"\t");
              output (outstrm, t);
              TextIO.output1 (outstrm, #"\n")
            end

  (* Time n runs of the benchmark *)
    fun time (n, outstrm, doit) = let
          fun loop 0 = (TextIO.output (outstrm, "],\n"))
            | loop i = (
                output (outstrm, timeOne doit);
                TextIO.output (outstrm, ", ");
                loop (i-1))
          in
            TextIO.output (outstrm, "\"runs\" : [");
            loop n
          end

  end

structure Measuring : sig
  val measure : TextIO.outstream * (unit -> 'a) -> unit
end = struct
  structure CI = Unsafe.CInterface
  val read' : unit -> word * word * word * word * word list =
        CI.c_function "SMLNJ-RunT" "gcCounterRead"
  val reset : bool -> unit =
        CI.c_function "SMLNJ-RunT" "gcCounterReset"
  fun read () = let
        (* results are:
         *   s     -- scaling factor for allocation counts
         *   a     -- scaled nursery allocation count
         *   a1    -- scaled first-generation allocation count
         *   p     -- scaled count of promotions to first generation
         *   ngcs  -- number of collections by generation
         *)
        val (s, a, a1, p, ngcs) = read'()
        val scale = Word.toLargeInt s
        in {
          nbAlloc = scale * Word.toLargeInt a,
          nbPromote = scale * Word.toLargeInt p,
          nGCs = List.map Word.toLargeInt ngcs
        } end

  fun measurementToString { nbAlloc, nbPromote, nGCs } = concat [
          "\"alloc\" : { \"nbAlloc\": ", IntInf.toString nbAlloc,
          ", \"nbPromote\" : ", IntInf.toString nbPromote, ", \"nGCs\" : [",
          String.concatWithMap "," IntInf.toString nGCs, "]}\n"
        ]

  fun report (outstrm, measurement) =
        TextIO.output (outstrm, measurementToString measurement)

  fun measure (outstrm, doit) = let
        (* val () = SMLofNJ.Internals.GC.messages true *)
        val () = reset true
        val _ = doit ()
        val measurement = read ()
        in
          report (outstrm, measurement)
        end
end
