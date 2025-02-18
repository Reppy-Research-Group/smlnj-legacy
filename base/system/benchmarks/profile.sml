CM.make "$smlnj-tdp/coverage.cm";
SMLofNJ.Internals.TDP.mode := true;

structure Profile : sig
  val profile : (unit -> unit) -> unit
end = struct
  structure C = Coverage
  fun profile doit =
    let val kinds = [C.functions, C.tail_calls, C.non_tail_calls]
    in  C.install ();
        doit ();
        C.hot_spots kinds 1000
    end
end
