structure FlowCFA :> CFA = struct

  structure LCPS = LabelledCPS
  structure LV   = struct
    open LambdaVar
    structure MonoSet = HashSetFn(Tbl.Key)
  end
  structure Syn  = SyntacticInfo
  type lvar = LV.lvar

  exception Unimp
  exception Impossible of string

  fun mapToList f vs = Vector.foldl (fn (v, acc) => f v :: acc) [] vs
  fun mapToVec  f vs = Vector.fromList (map f vs)
  fun concatWithMap str f vs = String.concatWith str (mapToList f vs)
  fun hashCombine (hash1, hash2) =
    (* C++ Boost's hash_combine *)
    Word.xorb (hash1, Word.+ (hash2,
                              (Word.+ (0wx9e3779b9,
                                       (Word.+ (Word.<< (hash1, 0w6),
                                                Word.>> (hash1, 0w2)))))))

  structure Value :> sig
    datatype t = Function of LCPS.function
               | Record   of lvar vector
               | Mutable  of lvar
               | ExternalFunction
               | Value    of LCPS.cty

    val hash : t -> word
    val same : t * t -> bool
    val toString : t -> string

    structure HashSet : MONO_HASH_SET where type Key.hash_key = t
  end = struct
    datatype t = Function of LCPS.function
               | Record   of lvar vector
               | Mutable  of lvar
               | ExternalFunction
               | Value    of LCPS.cty

    fun hash v =
      let val funtag = 0w0
          val rectag = 0w1
          val muttag = 0w2
          val extfun = 0w3
          val valtag = 0w4
          val hashvar = Word.fromInt o LV.toId
      in  case v
            of Function f => hashCombine (funtag, hashvar (#2 f))
             | Record vs => Vector.foldl
                              (fn (v, h) => hashCombine (h, hashvar v))
                              rectag vs
             | Mutable v => hashCombine (muttag, hashvar v)
             | ExternalFunction => hashCombine (extfun, 0w17)
             | Value _ => hashCombine (valtag, 0w17)
      end

    fun same (Function f1, Function f2) = LV.same (#2 f1, #2 f2)
      | same (Record vs1, Record vs2) =
          Vector.collate LV.compare (vs1, vs2) = EQUAL
      | same (Mutable v1, Mutable v2) = LV.same (v1, v2)
      | same (ExternalFunction, ExternalFunction) = true
      | same (Value ty1, Value ty2) =
          (case (ty1, ty2) (* Do we only care about the first level? *)
             of (CPS.NUMt _, CPS.NUMt _) => true
              | (CPS.PTRt _, CPS.PTRt _) => true
              | (CPS.FUNt, CPS.FUNt) => true
              | (CPS.FLTt _, CPS.FLTt _) => true
              | (CPS.CNTt, CPS.CNTt) => true
              | _ => false)
      | same _ = false

    fun toString (Function f) = LV.lvarName (#2 f) ^ "[f]"
      | toString (Record vs) =
          concat ["{", concatWithMap ", " LV.lvarName vs, "} [R]"]
      | toString (Mutable v) = concat [LV.lvarName v, "[REF]"]
      | toString ExternalFunction = "Extern"
      | toString (Value cty) = CPSUtil.ctyToString cty

    structure HashSet = HashSetFn(struct
      type hash_key = t
      val hashVal = hash
      val sameKey = same
    end)
  end

  infix 6 >-> -->

  structure Fact :> sig
    datatype t = >-> of lvar * lvar
               | --> of Value.t * lvar
               | /-- of LCPS.function
               | --/ of lvar

    val toString : t -> string
    val hash : t -> word
    val same : t * t -> bool

    structure HashSet : MONO_HASH_SET   where type Key.hash_key = t
    structure HashTbl : MONO_HASH_TABLE where type Key.hash_key = t
  end = struct
    datatype t = >-> of lvar * lvar
               | --> of Value.t * lvar
               | /-- of LCPS.function
               | --/ of lvar

    fun toString (x >-> y) = concat [LV.lvarName x, " >-> ", LV.lvarName y]
      | toString (v --> y) = concat [Value.toString v, " --> ", LV.lvarName y]
      | toString (/-- f) = concat ["/-- ", LV.lvarName (#2 f)]
      | toString (--/ v) = concat [LV.lvarName v, " --/"]

    fun hash f =
      let val com = hashCombine and hv = Word.fromInt o LV.toId
      in  case f
            of (x >-> y) => com (hv x, hv y)
             | (v --> y) => com (com (Value.hash v, hv y), 0w1)
             | (/-- f) => com (hv (#2 f), 0w2)
             | (--/ v) => com (hv v, 0w3)
      end

    fun same (x1 >-> y1, x2 >-> y2) =
          LV.same (x1, x2) andalso LV.same (y1, y2)
      | same (v1 --> y1, v2 --> y2) =
          Value.same (v1, v2) andalso LV.same (y1, y2)
      | same (/-- f1, /-- f2) = LV.same (#2 f1, #2 f2)
      | same (--/ v1, --/ v2) = LV.same (v1, v2)
      | same _ = false

    structure Key : HASH_KEY = struct
      type hash_key = t
      val hashVal = hash
      val sameKey = same
    end
    structure HashSet = HashSetFn(Key)
    structure HashTbl = HashTableFn(Key)
  end

  datatype fact  = datatype Fact.t
  datatype value = datatype Value.t
  datatype cexp  = datatype LCPS.cexp
  datatype either = datatype Either.either

  structure FactSet :> sig
    type t
    val mk : int -> t
    val add            : t -> Fact.t -> bool
    val member         : t -> Fact.t -> bool
    val forallValuesOf : t -> lvar -> (Value.t -> unit) -> unit
    val transitivity   : t -> Value.t * lvar -> (Fact.t -> unit) -> unit
    val dump : t -> unit
  end = struct
    type t = {
      (* row(i) = { j | i >-> j ∈ R }*)
      row    : LV.MonoSet.set LV.Tbl.hash_table,
      (* store(i) = { v | v --> i ∈ R }*)
      store  : Value.HashSet.set LV.Tbl.hash_table,
      (* sink = { v | --/ v } *)
      sink   : LV.MonoSet.set,
      (* escape = { f | /-- f } *)
      escape : LCPS.FunMonoSet.set
    }

    structure LVS = LV.MonoSet
    structure LVT = LV.Tbl
    structure VS  = Value.HashSet

    exception FactSet
    fun mk hint = {
      row = LV.Tbl.mkTable (hint, FactSet),
      store = LV.Tbl.mkTable (hint, FactSet),
      sink  = LV.MonoSet.mkEmpty hint,
      escape = LCPS.FunMonoSet.mkEmpty hint
    }

    fun add ({row, store, sink, escape}: t) =
      fn x >-> y =>
          (case LVT.find row x
             of SOME set =>
                  if LVS.member (set, y) then
                    false
                  else
                    (LVS.add (set, y); true)
              | NONE =>
                  (LVT.insert row (x, LVS.mkSingleton y); true))
       | v --> x =>
          (case LVT.find store x
             of SOME set =>
                  if VS.member (set, v) then false else (VS.add (set, v); true)
              | NONE =>
                  (LV.Tbl.insert store (x, VS.mkSingleton v); true))
       | /-- f =>
          if LCPS.FunMonoSet.member (escape, f) then
            false
          else
            (LCPS.FunMonoSet.add (escape, f); true)
       | --/ v =>
          if LVS.member (sink, v) then false else (LVS.add (sink, v); true)

    fun member ({row, store, sink, escape}: t) =
      fn x >-> y =>
           (case LVT.find row x
              of SOME set => LVS.member (set, y)
               | NONE     => false)
       | v --> x =>
           (case LVT.find store x
              of SOME set => VS.member (set, v)
               | NONE     => false)
       | /-- f =>
           LCPS.FunMonoSet.member (escape, f)
       | --/ v =>
           LVS.member (sink, v)

    fun forallValuesOf ({store, ...}: t) v f =
      (case LVT.find store v
         of SOME set => VS.app f set
          | NONE => ())

    fun transitivity (t as {row, ...}: t) (v, x) f =
      (case LVT.find row x
         of SOME set =>
              LVS.app (fn y => if add t (v --> y) then f (v --> y) else ()) set
          | NONE => ())

    fun dump ({row, store, sink, escape}: t) =
      let val puts = print o concat
          fun prow (x, set) =
            puts [LV.lvarName x, " >-> {",
                  String.concatWithMap " " LV.lvarName (LVS.listItems set),
                  "}\n"]
          fun pstore (x, vs) =
            puts [LV.lvarName x, " <-- {",
                  String.concatWithMap " " Value.toString (VS.listItems vs),
                  "}\n"]
      in  LVT.appi prow row;
          LVT.appi pstore store;
          puts ["/-- {",
                String.concatWithMap " " (LV.lvarName o #2)
                (LCPS.FunMonoSet.listItems escape),
                "}\n"];
          puts ["--/ {",
                String.concatWithMap " " LV.lvarName (LVS.listItems sink),
                "}\n"]
      end
  end

(*   structure FactSetRef :> sig *)
(*     type t *)
(*     val mk : int -> t *)
(*     val add            : t -> Fact.t -> bool *)
(*     val member         : t -> Fact.t -> bool *)
(*     val forallValuesOf : t -> lvar -> (Value.t -> unit) -> unit *)
(*     val transitivity   : t -> Value.t * lvar -> (Fact.t -> unit) -> unit *)
(*   end = struct *)
(*     fun forallValuesOf ({facts, ...}: ctx) x f = *)
(*       let fun find (v --> y) = if LV.same (x, y) then f v else () *)
(*             | find _ = () *)
(*       in  Fact.HashSet.app find facts *)
(*       end *)

(*     fun transitivity (ctx as {facts, ...}: ctx) (v, x) = *)
(*       let fun collect (x' >-> y, facts) = *)
(*                 if LV.same (x, x') then v --> y :: facts else facts *)
(*             | collect (_, facts) = facts *)
(*           val facts' = Fact.HashSet.fold collect [] facts *)
(*       in  List.app (fn f => remember (ctx, f)) facts' *)
(*       end *)

(*     fun member ({facts, ...}: ctx) fact = Fact.HashSet.member (facts, fact) *)
(*   end *)

  structure Context :> sig
    type ctx
    val mk : Syn.t -> ctx
    val remember : ctx * Fact.t -> unit
    val next : ctx -> Fact.t option
    val dump : ctx -> unit
    val forallValuesOf : ctx -> lvar -> (Value.t -> unit) -> unit
    val forallUsesOf   : ctx -> lvar -> (LCPS.cexp -> unit) -> unit
    val transitivity   : ctx -> Value.t * lvar -> unit
    val member : ctx -> Fact.t -> bool
    (* val summary : ctx -> unit *)
  end = struct
    type ctx = {
      todo  : Fact.t Queue.queue,
      facts : FactSet.t,
      syn   : Syn.t
    }

    fun mk syn = {
      todo=Queue.mkQueue (),
      facts=FactSet.mk 1024,
      syn=syn
    }

    fun remember ({todo, facts, ...}: ctx, fact) =
      if FactSet.add facts fact then Queue.enqueue (todo, fact) else ()

    fun next ({todo, ...}: ctx) = Queue.next todo

    fun forallUsesOf ({syn, ...}: ctx) x f =
      let val set = Syn.usePoints syn x
      in  LCPS.Set.app f set
      end

    fun forallValuesOf ({facts, ...}: ctx) = FactSet.forallValuesOf facts

    fun transitivity ({facts, todo, ...}: ctx) (v, x) =
      FactSet.transitivity facts (v, x) (fn f => Queue.enqueue (todo, f))

    fun member ({facts, ...}: ctx) f = FactSet.member facts f

    fun dump {todo, facts, syn=_} =
      (print "Context:\n";
       FactSet.dump facts;
       ())

    (* fun summary ({facts, ...}: ctx) = *)
    (*   (print "Escaping: {"; *)
    (*    Fact.HashSet.app (fn (/-- f) => print (LV.lvarName (#2 f) ^ ", ") *)
    (*                       | _ => ()) facts; *)
    (*    print "}\n") *)
  end

  fun label _ = raise Impossible "Label generated before closure conversion"
  fun offset _ = raise Impossible "Offset"
  val bogusTy = CPSUtil.BOGt

  (* r = (x1 : r1, x2 : r2, x3 : r3)
   * -----------------------------------
   * x1 >-> r1, x2 >-> r2, x3 >-> r3
   *
   * x = r.0       (r1, r2, r3) >-> r
   * -----------------------------------
   * r1 >-> x
   *
   *
   * r = makeref(a : r1)
   * -----------------------------------
   * REF r1 --> r
   *
   * x = !r   REF r1 --> r
   * -----------------------------------
   * r1 >-> x
   *
   *
   * r := x   REF r1 --> r
   * -----------------------------------
   * x >-> r1
   *)

  fun flowValue (value, dest) =
    (case value
       of (CPS.VAR v) => v >-> dest
        | (CPS.LABEL l) => label ()
        | (CPS.NUM n) => Value (CPS.NUMt (#ty n)) --> dest
        | (CPS.REAL r) => Value (CPS.FLTt (#ty r)) --> dest
        | (CPS.STRING s) => Value bogusTy --> dest
        | CPS.VOID => Value bogusTy --> dest)

  fun access (addr, value, CPS.OFFp 0) = flowValue (value, addr)
    | access (addr, value, CPS.OFFp i) = offset ()
    | access (addr, value, CPS.SELp _) =
        raise Fail "no select in accesspath before closure conversion"

  fun oneArg [x] = x
    | oneArg _   = raise Impossible "expected only one arg"

  fun twoArgs [x, y] = (x, y)
    | twoArgs _      = raise Impossible "expected two args"

  fun threeArgs [x, y, z] = (x, y, z)
    | threeArgs _         = raise Impossible "expected three args"

  fun varOf (CPS.VAR v) = v
    | varOf _           = raise Impossible "expected var"

  fun isFunTy (CPS.FUNt | CPS.CNTt) = true
    | isFunTy _ = false

  fun fromType (v, ty) =
    if isFunTy ty then ExternalFunction --> v else Value ty --> v

  fun initialize (syn, cps) =
    let
      val ctx = Context.mk syn
      fun add fact = Context.remember (ctx, fact)
      fun walkB (f as (kind, name, args, tys, body)) =
            (add (Function f --> name); walk body)
      and walk (RECORD (label, CPS.RK_VECTOR, values, dest, cexp)) =
            let fun build (_, value, CPS.OFFp 0) = flowValue (value, label)
                  | build (_, value, CPS.OFFp i) = offset ()
                  | build (_, value, CPS.SELp _) = raise Fail "desugar"
            in  add (Mutable label --> dest); app (add o build) values;
                walk cexp
            end
        | walk (RECORD (_, _, values, dest, cexp)) =
            let fun build (addr, CPS.VAR v, CPS.OFFp 0) : lvar = v
                  | build (addr, value, CPS.OFFp 0) =
                      (add (flowValue (value, addr)); addr)
                  | build (addr, value, CPS.OFFp i) = offset ()
                  | build (addr, value, CPS.SELp _) = raise Fail "desugar"
            in  add (Record (mapToVec build values) --> dest); walk cexp
            end
        | walk (SELECT (_, _, _, _, _, cexp)) = walk cexp
        | walk (OFFSET _) = offset ()
        | walk (APP _) = ()
        | walk (FIX (_, bindings, cexp)) = (app walkB bindings; walk cexp)
        | walk (SWITCH (_, _, _, branches)) = app walk branches
        | walk (BRANCH (_, _, _, _, te, fe)) = (walk te; walk fe)
        | walk (SETTER (_, _, _, cexp)) = walk cexp
        | walk (LOOKER (_, CPS.P.GETHDLR, _, dest, _, cexp)) =
            (add (ExternalFunction --> dest); walk cexp)
        | walk (LOOKER (_, _, _, _, _, cexp)) = walk cexp
        | walk (ARITH (_, _, _, dest, ty, cexp)) =
            (add (Value ty --> dest); walk cexp)
        | walk (PURE (label, CPS.P.MAKEREF, values, dest, _, cexp)) =
            let val v = oneArg values
            in  add (flowValue (v, label)); add (Mutable label --> dest);
                walk cexp
            end
        | walk (PURE (label, (CPS.P.RAWRECORD _ | CPS.P.NEWARRAY0), _,
                      dest, _, cexp)) =
            (add (Mutable label --> dest); walk cexp)
        | walk (PURE (label, _, _, _, _, cexp)) = walk cexp
        | walk (RCC (_, _, _, _, _, results, cexp)) =
            (app (add o fromType) results; walk cexp)
    in
      add (/-- cps); walkB cps; ctx
    end

  fun run ctx =
    let
      fun add fact = Context.remember (ctx, fact)
      val forallValuesOf = Context.forallValuesOf ctx
      val forallUsesOf = Context.forallUsesOf ctx
      val transitivity = Context.transitivity ctx
      val member = Context.member ctx

      fun propagate (/-- (function as (kind, name, args, tys, body))) =
            (ListPair.appEq (add o fromType) (args, tys))
        | propagate (x >-> y) = forallValuesOf x (fn v => add (v --> y))
        | propagate (--/ x) = forallValuesOf x escape
        | propagate (v --> x) =
            if member (--/ x) then
              escape v
            else
              (transitivity (v, x); propagateValue (v, x))
      and propagateValue (Function (func as (_, _, formals, _, _)), x) =
            forallUsesOf x
              (fn APP (_, f, args) =>
                    if LV.same (x, varOf f) then
                      ListPair.appEq (add o flowValue) (args, formals)
                    else ()
                | SETTER (_, CPS.P.SETHDLR, _, _) => add (/-- func)
                | _ => ())
        | propagateValue (ExternalFunction, x) =
            forallUsesOf x
              (fn APP (_, f, args) =>
                    let fun markEscape (CPS.VAR v) = add (--/ v)
                          | markEscape _ = ()
                    in  if LV.same (x, varOf f) then
                          List.app markEscape args
                        else ()
                    end
                | _ => ())
        | propagateValue (Record rs, x) =
            forallUsesOf x
              (fn SELECT (_, i, _, dest, _, _) =>
                    if i < Vector.length rs then
                      add (Vector.sub (rs, i) >-> dest)
                    else ()
                | _ => ())
        | propagateValue (Mutable r, x) =
            forallUsesOf x
              (fn SETTER (_, (CPS.P.ASSIGN|CPS.P.UNBOXEDASSIGN), args, _) =>
                    let val (_, rhs) = twoArgs args
                    in  add (flowValue (rhs, r))
                    end
                | LOOKER (_, (CPS.P.DEREF | CPS.P.SUBSCRIPT), _, dest, _, _) =>
                    add (r >-> dest)
                | _ => ())
        | propagateValue (Value _, x) =
            forallUsesOf x
              (fn SELECT (_, _, value, dest, ty, _) =>
                    add (fromType (dest, ty))
                | APP (_, f, args) =>
                    () (* Uniform value cannot be used as a function *)
                | LOOKER (_, _, _, dest, ty, _) =>
                    add (fromType (dest, ty))
                | _ => ())
      and escape (Function f) = add (/-- f)
        | escape (Record vars) =
            Vector.app (fn v =>
              if not (member (--/ v)) then
                (add (--/ v); forallValuesOf v escape)
              else ()) vars
        | escape (Mutable v) =
              if not (member (--/ v)) then
                (add (--/ v); forallValuesOf v escape)
              else ()
        | escape (ExternalFunction | Value _) = ()

      fun dump n = (print ("\r" ^ Int.toString n))

      fun loop n =
        (case Context.next ctx
           of NONE => ()
            | SOME fact => (dump n; propagate fact; loop (n + 1)))
    in
      loop 0
    end


  fun timeit str thunk =
    let
      val start = Time.now ()
      val result = thunk ()
      val stop = Time.now ()
      val diff = Time.- (stop, start)
      val () = (print (str ^ Time.toString diff); print "\n")
    in
      result
    end

  fun analyze (syn, cps) =
    let val ctx = initialize (syn, cps)
        (* val () = Context.dump ctx *)
        val () = timeit "flow-cfa" (fn () => run ctx)
        val () = print "\n"
        val () = Context.dump ctx
    in  CallGraph.bogus ()
    end
end
