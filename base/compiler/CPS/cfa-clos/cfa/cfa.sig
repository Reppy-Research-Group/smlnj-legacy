signature CALL_GRAPH = sig
  type t

  val build : {
    cps: LabelledCPS.function,
    lookup : CPS.lvar -> 'value,
    filter :'value -> LabelledCPS.function list option,
    escapingLambdas: LabelledCPS.function vector
  } -> t

end

signature CFA = sig

  structure CallGraph : CALL_GRAPH

  val analyze : LabelledCPS.function -> CallGraph.t

end
