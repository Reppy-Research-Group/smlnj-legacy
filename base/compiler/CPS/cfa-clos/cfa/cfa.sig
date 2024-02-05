signature CFA = sig

  val analyze : SyntacticInfo.t * LabelledCPS.function -> CallGraph.t

end
