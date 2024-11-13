functor FlatteningAnalysis(MachSpec : MACH_SPEC) :> sig
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

  val maxgpregs = MachSpec.numRegs
  val maxfpregs = MachSpec.numFloatRegs - 2  (* need 1 or 2 temps *)
  val numCSgpregs = MachSpec.numCalleeSaves
  val numCSfpregs = MachSpec.numFloatCalleeSaves
  val unboxedfloat = MachSpec.unboxedFloats
  fun isFltCty (CPS.FLTt _) = unboxedfloat
    | isFltCty _ = false
  fun numgp (m,CPS.CNTt::z) = numgp(m-numCSgpregs-1,z)
    | numgp (m,x::z) = if isFltCty(x) then numgp(m,z) else numgp(m-1,z)
    | numgp (m,[]) = m

  fun numfp (m,CPS.CNTt::z) = numfp(m-numCSfpregs,z)
    | numfp (m,x::z) = if isFltCty(x) then numfp(m-1,z) else numfp(m,z)
    | numfp (m,[]) = m

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

  fun envusage (repr: D.repr, web: W.t) =
    let fun collect (f, D.Closure { code, env }, usage) =
          (case env
             of D.Flat [] => usage
              | (D.Flat _ | D.FlatAny _) => raise Fail "wrong stage"
              | D.Boxed e => EnvID.Map.insert (usage, e, f))
    in  LCPS.FunMap.foldli collect EnvID.Map.empty repr
    end

  fun flattenableWeb (census, usage, web) =
    let fun flattenableEnv flattenable env =
          (case EnvID.Map.find (usage, env)
             of NONE => (* shared env *) false
              | SOME f =>
                  let val w = W.webOfFun (web, f)
                  in  W.Set.member (flattenable, w)
                  end)
        fun process (w, _, flattenable: W.Set.set) =
          (case W.Map.find (census, w)
             of NONE => W.Set.add (flattenable, w)
              | SOME envs =>
                  if List.all (flattenableEnv flattenable) envs then
                    W.Set.add (flattenable, w)
                  else
                    flattenable)
        (* It is important that this calculates the _least_ fixed point because
         * we don't want a self-referential web --- a web function captures a
         * variable of the same web, as is common in non-tail recursive
         * functions --- to be marked as flattenable. *)
        fun fixpt (n, flattenable) =
          let val flattenable' = W.fold process flattenable web
          in  if W.Set.equal (flattenable, flattenable') then
                flattenable
              else
                fixpt (n + 1, flattenable')
          end
    in  fixpt (0, W.Set.empty)
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

  (* fun mutrec f = Vector.length (S.groupFun syn (S.groupOf syn f)) > 1 *)
  (* Analyze bandwidth *)

  datatype bandwidth = Escape | MaxOf of int | Unlimited
  fun mergeBW (Escape, _) = Escape
    | mergeBW (_, Escape) = Escape
    | mergeBW (bw, Unlimited) = bw
    | mergeBW (Unlimited, bw) = bw
    | mergeBW (MaxOf i, MaxOf i') = MaxOf (Int.min (i, i'))
  fun bandwidthToString Escape = "Escape"
    | bandwidthToString (MaxOf i) = "Max=" ^ Int.toString i
    | bandwidthToString Unlimited = "Unlim"

  fun webBandwidth (syn, repr, web) =
    let (* Step 1: figure out the user web that each continuation web is passed
         * to. *)
        datatype cont_data = KnownContOf of W.id list
                           | EscapingCont
        fun mergeContData (EscapingCont, _) = EscapingCont
          | mergeContData (_, EscapingCont) = EscapingCont
          | mergeContData (KnownContOf id1, KnownContOf id2) =
              KnownContOf (id1 @ id2)
        fun contVarOf ((_, _, args, tys, _): LCPS.function) =
          (case (args, tys)
             of (c :: args, CPS.CNTt :: tys) => SOME c
              | _ => NONE)
        fun mapPartialV f vector =
          Vector.foldr (fn (x, lst) =>
            (case f x of NONE => lst | SOME y => y :: lst)
          ) [] vector
        fun checkSameWeb (c, acc) =
          let val w =
                (case W.webOfVar (web, c)
                   of NONE => raise Fail "Unassigned web for fun arg"
                    | SOME w => w)
          in  case acc
                of NONE => SOME w
                 | SOME w' =>
                     if W.same (w, w') then SOME w else raise Fail "??????"
          end
        fun checkedInsert (cont, w, data) =
          (case W.Map.find (cont, w)
             of NONE => W.Map.insert (cont, w, data)
              | SOME _ => raise Fail "double insert")
        val insert = W.Map.insertWith mergeContData
        fun collect (id, { defs, uses, polluted=true, kind=W.Cont }, cont) =
              W.Map.insert (cont, id, EscapingCont)
          | collect (id, { defs, uses, polluted=true, kind=W.User }, cont) =
              cont
          | collect (id, { defs, uses, polluted=false, kind=W.Cont }, cont) =
              cont
          | collect (id, { defs, uses, polluted=false, kind=W.User }, cont) =
              let val contVars = mapPartialV contVarOf defs
              in  case foldl checkSameWeb NONE contVars
                    of NONE => cont
                     | SOME w =>
                         if W.polluted (web, w) then
                           cont
                         else
                           insert (cont, w, KnownContOf [id])
              end
        val cont = W.fold collect W.Map.empty web
        (* val () = W.Map.appi (fn (cid, use) => *)
        (*   app print [W.idToString cid, " used by ", *)
        (*              (case use of EscapingCont => "escape" *)
        (*                         | KnownContOf uids => *)
        (*                             String.concatWithMap "," W.idToString uids), *)
        (*              "\n"] *)
        (* ) cont *)
        (* Step 2: When a continuation passes through a function, if the
         * function is singly known, then the bandwidth is unlimited, but if the
         * function is not a direct call, the bandwidth is the remaining
         * available registers *)
        fun numgp (m, CPS.CNTt :: z) = numgp (m - 1, z)
          | numgp (m, x :: z) =
             if isFltCty x then numgp (m, z) else numgp (m - 1, z)
          | numgp (m, []) = m
        fun directCall defs =
          if Vector.length defs > 1 then
            false
          else
            let val f = Vector.sub (defs, 0)
                val D.Closure { code, ... } = LCPS.FunMap.lookup (repr, f)
            in  case code
                  of D.Direct _ => true
                   | _ => false
            end
        fun getWebBandwidth w =
          let val { defs, ... } = W.content (web, w)
          in  if directCall defs then
                Unlimited
              else
                let fun bw (_, _, _, tys, _) = numgp (maxgpregs - 2, tys)
                    val minBW = Vector.foldl (fn (f, bw') =>
                      Int.min (bw f, bw')
                    ) maxgpregs defs
                in  MaxOf minBW
                end
          end
        fun getBandwidth (contw, EscapingCont) = Escape
          | getBandwidth (contw, KnownContOf ws) =
              let val callsiteBW = getWebBandwidth contw
                  val passingBW  = foldl (fn (w, bw) =>
                    mergeBW (bw, getWebBandwidth w)
                  ) Unlimited ws
              in  mergeBW (callsiteBW, passingBW)
              end
    in  W.Map.mapi getBandwidth cont
    end

  fun selfRefFlattenableWeb (census, usage, web) =
    let fun usedBy id selfref env =
          (case EnvID.Map.find (usage, env)
             of NONE => false
              | SOME f =>
                  let val w = W.webOfFun (web, f)
                  in  W.same (w, id) orelse W.Set.member (selfref, w)
                  end)
        val usedBy = fn id => fn selfref => fn env =>
          let 
              (* val () = print ("selfref? " ^ EnvID.toString env) *)
              val result = usedBy id selfref env
              (* val () = print (if result then " true\n" else " false\n") *)
          in  result
          end
        fun process (w, _, selfref : W.Set.set) =
          (case W.Map.find (census, w)
             of NONE => W.Set.add (selfref, w)
              | SOME [_] => W.Set.add (selfref, w)
              | SOME envs =>
                  if List.all (usedBy w selfref) envs then
                    W.Set.add (selfref, w)
                  else
                    selfref)
        fun fixpt (n, selfref) =
          let val selfref' = W.fold process selfref web
          in  if W.Set.equal (selfref, selfref') then
                selfref
              else
                fixpt (n + 1, selfref')
          end
    in  fixpt (0, W.Set.empty)
    end

  fun analyzeArity
    (policy : int * int -> int)
    (flattenable : W.id -> bool)
    (repr, heap, web) =
    let val arityTbl = W.Tbl.mkTable (64, Fail "arity table")
        val insert = W.Tbl.insert arityTbl
        val lookup = W.Tbl.lookup arityTbl
        val find = W.Tbl.find arityTbl
        fun defaultArity W.Cont = SOME (numCSgpregs + 1)
          | defaultArity W.User = SOME 1
        fun arityOfS (suspended, slot) =
          (case slot
             of D.EnvID e => SOME 1
              | D.Var (v, ty) =>
                  (case W.webOfVar (web, v)
                     of SOME w => arityOfW (suspended, w)
                      | NONE =>
                          (case ty of CPS.CNTt => defaultArity W.Cont
                                    | _ => defaultArity W.User))
              | D.Code _ => SOME 1
              | (D.Expand _ | D.ExpandAny _ | D.Null) =>
                  raise Fail "wrong stage")
        and arityOfE (suspended, e) =
          (case EnvID.Map.lookup (heap, e)
             of D.RawBlock _ => SOME 1
              | D.Record (_, true) => SOME 1
              | D.Record (slots, false) =>
                  let fun collect (s, NONE) = NONE
                        | collect (s, SOME ar) =
                            (case arityOfS (suspended, s)
                               of NONE => NONE
                                | SOME ar' => SOME (ar + ar'))
                  in  foldl collect (SOME 0) slots
                  end)
        and arityOfF' (suspended, f) =
          (case LCPS.FunMap.lookup (repr, f)
             of D.Closure {env=(D.Flat []), ... } => SOME 0
              | D.Closure {env=(D.Flat _ | D.FlatAny _), ...} =>
                  raise Fail "wrong stage"
              | D.Closure {env=D.Boxed e, ...} => arityOfE (suspended, e))
        and arityOfF (suspended, f) =
          let val result = arityOfF' (suspended, f)
              (* val () = *)
              (*   (case result *)
              (*      of SOME i => app print [LV.lvarName (#2 f), " arity: ", *)
              (*                   Int.toString i, "\n"] *)
              (*       | NONE => app print [LV.lvarName (#2 f), " arity: NONE\n"]) *)
          in  result
          end
        and resolveArity (suspended, defs) =
          let fun collect (f, NONE) = arityOfF (suspended, f)
                | collect (f, SOME ar) =
                    (case arityOfF (suspended, f)
                       of NONE => SOME ar
                        | SOME ar' => SOME (policy (ar, ar')))
          in  Vector.foldl collect NONE defs
          end
        and arityOfW' (suspended, w) =
          (case W.content (web, w)
             of { polluted=true, kind, ... } => defaultArity kind
              | { defs, kind, ... } =>
                  if flattenable w then
                    resolveArity (suspended, defs)
                  else
                    defaultArity kind)
        and arityOfW (suspended, w) : int option =
          if W.Set.member (suspended, w) then
            NONE
          else
            (case find w
               of SOME ar => ar
                | NONE   =>
                    let 
                        (* val () = print ("calculating arity for " ^ W.idToString *)
                    (* w ^ "\n") *)
                        val result =
                          (case arityOfW' (W.Set.add (suspended, w), w)
                             of SOME arity => SOME arity
                              | NONE => NONE)
                        (* val () = print ("result=" ^ (case result of SOME i => *)
                        (* Int.toString i | NONE => "NONE") ^ "\n") *)
                    in  insert (w, result); result
                    end)
        val () =
          W.fold (fn (id, _, ()) => ignore (arityOfW (W.Set.empty, id))) () web
        (* val () = app print ["ArityTbl:\n"] *)
        (* val () = W.Tbl.appi *)
        (*   (fn (i, SOME ar) => *)
        (*      print (W.idToString i ^ " => " ^ Int.toString ar ^ "\n") *)
        (*     | (i, NONE) => *)
        (*      print (W.idToString i ^ " => NONE\n") *)
        (*   ) arityTbl *)
    in  lookup
    end


  fun arityOf (repr, heap, f) =
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

  fun resolveArity
    (policy: int * int -> int)
    (D.T {repr, allo, heap})
    (defs : LCPS.function vector) =
    let fun collect (f, NONE) = SOME (arityOf (repr, heap, f))
          | collect (f, SOME a) = SOME (policy (arityOf (repr, heap, f), a))
    in  case Vector.foldl collect NONE defs
          of NONE => raise Fail "0-size web"
           | SOME ar => ar
    end

  val liberally = Int.max
  val conservatively = Int.min

  fun medium (dec as D.T {repr, allo, heap}, web: W.t, syn: S.t) =
    (* Flatten return continuation to known functions *)
    let val census = webcensus (heap, web)
        val usage = envusage (repr, web)
        val flattenable = flattenableWeb (census, usage, web)
        val bandwidth = webBandwidth (syn, repr, web)
        val selfRef   = selfRefFlattenableWeb (census, usage, web)
        (* val () = app print [ *)
        (*   "Flattenable: [", String.concatWithMap "," W.idToString *)
        (*   (W.Set.listItems flattenable), "]\n"] *)
        (* val () = app print [ *)
        (*   "SelfRef: [", String.concatWithMap "," W.idToString *)
        (*   (W.Set.listItems selfRef), "]\n"] *)
        (* val () = app print [ "Bandwidth:\n" ] *)
        (* val () = W.Map.appi (fn (id, bw) => app print [ *)
        (*   W.idToString id, " : ", bandwidthToString bw, "\n" ] *)
        (* ) bandwidth *)
        (* val () = app print [ "Reminder: maxgpregs=", Int.toString maxgpregs, *)
        (* "\n"] *)

        val webArity = analyzeArity liberally (fn w => W.Set.member (flattenable, w)) (repr, heap, web)

        val resolve = resolveArity liberally dec

        fun defaultArity (id, info: W.info) =
          (case info
             of { kind=W.Cont, ... } => Fixed 3
              | { polluted=true, kind=W.User, ... } => One
              | _ => One)

        fun contWebArity (id, info: W.info) =
          (case info
             of { polluted=false, kind=W.Cont, defs, uses } =>
                  (* if not (W.Set.member (flattenable, id)) then *)
                  (*   defaultArity (id, info) *)
                  (* else *)
                    (case W.Map.find (bandwidth, id)
                       of (NONE | SOME Escape) => defaultArity (id, info)
                        | SOME Unlimited =>
                            (case webArity id
                               of SOME ar => Fixed ar
                                | NONE => defaultArity (id, info))
                            (* Fixed (resolve defs) *)
                        | SOME (MaxOf i) =>
                            (case webArity id
                               of SOME ar =>
                                    Fixed (Int.max (numCSgpregs, Int.min (i, ar)))
                                | NONE => defaultArity (id, info)))
                            (* Fixed (Int.max (resolve defs, i))) *)
              | _ => defaultArity (id, info))

        fun knownArity (id, info: W.info) =
          (case info
             of { polluted=false, defs=(#[f]), uses=(#[v]), ... } =>
                  if inDataStructureOne syn v then
                    One
                  else if arityOf (repr, heap, f) = 0 then
                    Fixed 0
                  else if W.Set.member (flattenable, id) then
                    Any f
                  else
                    Fixed 1
              | _ => contWebArity (id, info))

        fun arity id = knownArity (id, W.content (web, id))

    in  arity
    end

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
        val usage = envusage (repr, web)
        val flattenable = flattenableWeb (census, usage, web)
        fun arity id =
          (case Web.content (web, id)
             of { polluted=false, defs=(#[f]), uses=(uses as #[_]), ... } =>
                  if inDataStructure syn uses then
                    One
                  else if arityOf f = 0 then
                    Fixed 0
                  else if W.Set.member (flattenable, id) then
                    Any f
                  else
                    Fixed 1
              | { kind=W.Cont, ... } => Fixed 3
              | { polluted=true, kind=W.User, ... } => One
              | _ => One)
    in  arity
    end
end
