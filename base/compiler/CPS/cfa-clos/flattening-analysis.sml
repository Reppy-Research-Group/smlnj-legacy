structure FlatteningAnalysis :> sig
  datatype arity = One | Fixed of int | Any of LabelledCPS.function
  type decision = Web.id -> arity
  val toString : arity -> string

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

  datatype arity = One | Fixed of int | Any of LCPS.function
  type decision = Web.id -> arity

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
             of D.Record (slots, _) => foldl (scan env) census slots
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

  fun medium (D.T {repr, allo, heap}, web: W.t, syn: S.t) = raise Fail "unimp"
    (* let val census = webcensus (heap, web) *)
    (*     fun isShared e = *)
    (*       (case EnvID.Map.lookup (heap, e) *)
    (*          of D.Record (_, shared) => shared *)
    (*           | D.RawBlock _ => raise Fail "unexpected raw block") *)
    (*     fun usecnt id = *)
    (*       (case W.Map.find (census, id) *)
    (*          of NONE => 0 *)
    (*           | SOME envs => List.length envs) *)
    (*     fun defaultArity (v, ty) = *)
    (*       (case (S.knownFun syn v, ty) *)
    (*          of (SOME _, CPS.CNTt) => 3 *)
    (*           | (NONE  , CPS.CNTt) => 4 *)
    (*           | _ => 1) *)
    (*     fun arityOfV (flatten, v, ty) = *)
    (*       (case W.webOfVar (web, v) *)
    (*          of SOME id => Option.getOpt (W.Map.find (flatten, id), *)
    (*                                       defaultArity (v, ty)) *)
    (*           | NONE => defaultArity (v, ty)) *)
    (*     fun arityOfSlot (flatten, D.Var (v, ty)) = arityOfV (flatten, v, ty) *)
    (*       | arityOfSlot (flatten, D.Expand _) = raise Fail "expand before flat" *)
    (*       | arityOfSlot (flatten, _) = 1 *)
    (*     fun arityOfSlots (flatten, slots) = *)
    (*       foldl (fn (s, acc) => acc + arityOfSlot (flatten, s)) 0 slots *)
    (*     fun mutrec f = *)
    (*       Vector.length (S.groupFun syn (S.groupOf syn f)) > 1 *)
    (*     fun arityOf (flatten, f) = *)
    (*       (case LCPS.FunMap.lookup (repr, f) *)
    (*          of D.Closure {env=D.Flat slots, ...} => *)
    (*               arityOfSlots (flatten, slots) *)
    (*           | D.Closure {env=(D.FlatAny e | D.Boxed e), ...} => *)
    (*               if isShared e then *)
    (*                 1 *)
    (*               else if mutrec f then *)
    (*                 1 *)
    (*               else *)
    (*                 (case EnvID.Map.lookup (heap, e) *)
    (*                    of D.Record (slots, _) => arityOfSlots (flatten, slots) *)
    (*                     | D.RawBlock _ => 1)) *)
    (*     (1* val arityOf = fn (flatten, f) => *1) *)
    (*     (1*   let val n = arityOf (flatten, f) *1) *)
    (*     (1*   in  print (LV.lvarName (#2 f) ^ " ---> " ^ Int.toString n ^ "\n"); *1) *)
    (*     (1*       n *1) *)
    (*     (1*   end *1) *)
    (*     fun collect (id, info: W.info, flatten: int W.Map.map) = *)
    (*       (case info *)
    (*          of { polluted=false, defs=(#[f]), uses=(uses as #[_]), ... } => *)
    (*               if inDataStructure syn uses then *)
    (*                 flatten *)
    (*               else if arityOf (flatten, f) = 0 then *)
    (*                 W.Map.insert (flatten, id, 0) *)
    (*               else if usecnt id < 1 then *)
    (*                 W.Map.insert (flatten, id, arityOf (flatten, f)) *)
    (*               else *)
    (*                 flatten *)
    (*           | { polluted=true, kind=W.User, ... } => flatten *)
    (*           | { polluted=true, kind=W.Cont, ... } => W.Map.insert (flatten, id, 3) *)
    (*           | _ => flatten) *)
    (*     fun update flatten = W.fold collect flatten web *)
    (*     fun fixpt (n, flatten) = *)
    (*       let *)
    (*           (1* val () = print ("iter " ^ Int.toString n ^ "\n") *1) *)
    (*           val flatten' = update flatten *)
    (*       in  if W.Map.collate Int.compare (flatten, flatten') = EQUAL then *)
    (*             flatten' *)
    (*           else *)
    (*             fixpt (n + 1, flatten') *)
    (*       end *)
    (*     (1* val () = print "Flatten:\n" *1) *)
    (*     (1* val () = D.dump (D.T {repr=repr, allo=allo, heap=heap}, syn) *1) *)
    (*     val flatten = fixpt (0, W.Map.empty) *)
    (*     fun arity id = *)
    (*       (case Web.content (web, id) *)
    (*          of { kind=W.Cont, uses=(#[_]), ... } => W.Map.find (flatten, id) *)
    (*           | { kind=W.Cont, ... } => SOME 3 *)
    (*           | _ => W.Map.find (flatten, id)) *)
    (* in  arity *)
    (* end *)

  fun toString One = "One"
    | toString (Fixed n) = Int.toString n
    | toString (Any _) = "Any"

  fun simple (D.T {repr, allo, heap}, web: W.t, syn: S.t) =
    let fun arityOf f =
          (case LCPS.FunMap.lookup (repr, f)
             of D.Closure {env=D.Flat slots, ...} => List.length slots
              | D.Closure {env=D.FlatAny e, ...} =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record (slots, _) => List.length slots
                      | D.RawBlock _ => 1)
              | D.Closure {env=D.Boxed e, ...} =>
                  (case EnvID.Map.lookup (heap, e)
                     of D.Record (slots, _) => List.length slots
                      | D.RawBlock _ => 1))
        val census = webcensus (heap, web)
        fun usecnt id =
          (case W.Map.find (census, id)
             of NONE => 0
              | SOME envs => List.length envs)
        fun arity id =
          (case Web.content (web, id)
             of { kind=W.Cont, ... } => Fixed 3
              | { polluted=true, kind=W.User, ... } => One
              | { polluted=false, defs=(#[f]), uses=(uses as #[_]), ... } =>
                  if inDataStructure syn uses then
                    One
                  else if arityOf f = 0 then
                    Fixed 0
                  else if usecnt id = 0 then
                    Any f
                  else
                    Fixed 1
              | _ => One)
    in  arity
    end
end
