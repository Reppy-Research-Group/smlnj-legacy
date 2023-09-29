signature CALL_GRAPH = sig
  type t

  val new : unit -> t
  val add : t * CPS.lvar * CPS.lvar -> unit

  val callers : t * CPS.lvar -> CPS.lvar list
  val callees : t * CPS.lvar -> CPS.lvar list

  val isCaller : t -> CPS.lvar * CPS.lvar -> bool
  val isCallee : t -> CPS.lvar * CPS.lvar -> bool
end

signature CFA = sig

  structure CallGraph : CALL_GRAPH

  val analyze : LabelledCPS.function -> CallGraph.t

end
