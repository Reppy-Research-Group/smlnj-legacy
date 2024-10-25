structure FlatteningAnalysis :> sig
  type decision = Web.id -> int option

  val simple : ClosureDecision.t * Web.t * SyntacticInfo.t -> decision
end = struct
  structure CF = ControlFlow
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo
  structure W = Web

  type decision = Web.id -> int option

  fun simple (D.T {repr, allo, heap}, web: W.t, syn: S.t) =
    let fun inDataStructureOne name =
          let fun construct (LCPS.RECORD _) = true
                | construct (LCPS.PURE _) = true
                | construct (LCPS.SETTER _) = true
                | construct (LCPS.LOOKER _) = true
                | construct (LCPS.ARITH _) = true
                | construct _ = false
              val uses = S.usePoints syn name
          in  LCPS.Set.exists construct uses
          end
        fun inDataStructure uses = Vector.exists inDataStructureOne uses
        fun arity id =
          (case Web.content (web, id)
             of { kind=W.Cont, ... } => SOME 3
              | { polluted=true, kind=W.User, ... } => NONE
              | { polluted=false, defs=(#[f]), uses=(uses as #[_]), ... } =>
                  if inDataStructure uses then
                    NONE
                  else
                    SOME 1
              | _ => NONE)
    in  arity
    end
end
