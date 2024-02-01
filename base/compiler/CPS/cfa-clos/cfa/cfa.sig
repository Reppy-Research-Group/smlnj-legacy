signature CFA = sig

  val analyze : SyntacticInformation.t * LabelledCPS.function -> CallGraph.t

end
