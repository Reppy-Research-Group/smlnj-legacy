structure FlatteningAnalysis :> sig
  type decision = Web.id -> int option

  val simple : ClosureDecision.t * Web.t * SyntacticInfo.t -> decision
  val medium : ClosureDecision.t * Web.t * SyntacticInfo.t -> decision
end = struct
  structure CF = ControlFlow
  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo
  structure W = Web

  type decision = Web.id -> int option

  fun webcensus (heap: D.heap, web: W.t) =
    let fun usedBy (census, w, env) =
          (case W.Map.find (census, w)
             of NONE => W.Map.insert (census, w, [env])
              | SOME envs => W.Map.insert (census, w, env :: envs))
        fun scan env (D.Var (v, _), census) =
              (case W.webOfVar (web, v)
                 of NONE => census
                  | SOME w => usedBy (census, w, env))
          | scan env (D.Expand _, census) = raise Fail "expand before flatten"
          | scan env (_, census) = census
        fun collect (env, object, census: EnvID.t list W.Map.map) =
          (case object
             of D.Record slots => foldl (scan env) census slots
              | D.RawBlock _ => census)
    in  EnvID.Map.foldli collect W.Map.empty heap
    end

  fun inDataStructureOne syn name =
    let fun construct (LCPS.RECORD _) = true
          | construct (LCPS.PURE _) = true
          | construct (LCPS.SETTER _) = true
          | construct (LCPS.LOOKER _) = true
          | construct (LCPS.ARITH _) = true
          | construct _ = false
        val uses = S.usePoints syn name
    in  LCPS.Set.exists construct uses
    end

  fun inDataStructure syn uses = Vector.exists (inDataStructureOne syn) uses

  fun medium (D.T {repr, allo, heap}, web: W.t, syn: S.t) =
    let val census = webcensus (heap, web)
        fun usecnt id =
          (case W.Map.find (census, id)
             of NONE => 0
              | SOME envs => List.length envs)
        fun arityOfV (flatten, v, ty) =
          (case W.webOfVar (web, v)
             of SOME id => Option.getOpt (W.Map.find (flatten, id), 0) + 1
              | NONE => (case ty of CPS.CNTt => 4 | _ => 1))
        fun arityOfSlot (flatten, D.Var (v, ty)) = arityOfV (flatten, v, ty)
          | arityOfSlot (flatten, D.Expand _) = raise Fail "expand before flat"
          | arityOfSlot (flatten, _) = 1
        fun arityOfSlots (flatten, slots) =
          foldl (fn (s, acc) => acc + arityOfSlot (flatten, s)) 0 slots
        fun arityOf (flatten, f) =
          (case LCPS.FunMap.lookup (repr, f)
             of D.Closure {env=D.Flat slots, ...} =>
                  arityOfSlots (flatten, slots)
              | D.Closure {env=D.Boxed e, ...} =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record slots => arityOfSlots (flatten, slots)
                      | D.RawBlock _ => 1))
        fun collect (id, info: W.info, flatten: int W.Map.map) =
          (case info
             of { polluted=false, defs=(#[f]), uses=(uses as #[_]), ... } =>
                  if inDataStructure syn uses then
                    flatten
                  else if arityOf (flatten, f) = 0 then
                    W.Map.insert (flatten, id, 0)
                  else if usecnt id = 0 then
                    W.Map.insert (flatten, id, arityOf (flatten, f))
                  else
                    flatten
              | { polluted=true, kind=W.User, ... } => flatten
              | { kind=W.Cont, ... } => W.Map.insert (flatten, id, 3)
              | _ => flatten)
        fun update flatten = W.fold collect flatten web
        fun fixpt (n, flatten) =
          let val () = print ("iter " ^ Int.toString n ^ "\n")
              val flatten' = update flatten
          in  if W.Map.collate Int.compare (flatten, flatten') = EQUAL then
                flatten'
              else
                fixpt (n + 1, flatten')
          end
        val flatten = fixpt (0, W.Map.empty)
        fun arity id = W.Map.find (flatten, id)
    in  arity
    end

  fun simple (D.T {repr, allo, heap}, web: W.t, syn: S.t) =
    let fun arityOf f =
          (case LCPS.FunMap.lookup (repr, f)
             of D.Closure {env=D.Flat slots, ...} => List.length slots
              | D.Closure {env=D.Boxed e, ...} =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record slots => List.length slots
                      | D.RawBlock _ => 1))
        (* val census = webcensus (heap, web) *)
        (* fun usecnt id = *)
        (*   (case W.Map.find (census, id) *)
        (*      of NONE => 0 *)
        (*       | SOME envs => List.length envs) *)
        fun arity id =
          (case Web.content (web, id)
             of { kind=W.Cont, ... } => SOME 3
              | { polluted=true, kind=W.User, ... } => NONE
              | { polluted=false, defs=(#[f]), uses=(uses as #[_]), ... } =>
                  if inDataStructure syn uses then
                    NONE
                  else if arityOf f = 0 then
                    SOME 0
                  else
                    SOME 1
              | _ => NONE)
    in  arity
    end
end
