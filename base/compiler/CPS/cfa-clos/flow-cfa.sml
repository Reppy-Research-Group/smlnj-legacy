structure FlowCFA :> sig
  type functions = { known: LabelledCPS.function list, unknown: bool }
  type variables = { known: LabelledCPS.lvar list, escape: bool }
  type result = {
    lookup: LambdaVar.lvar -> functions option,
    flow  : LabelledCPS.function -> variables
  }
  val analyze : SyntacticInfo.t * LabelledCPS.function -> result
end = struct

  structure LCPS = LabelledCPS
  structure Syn  = SyntacticInfo

  exception Unimp
  exception Impossible of string

  structure SipHash13 :> sig
    type state

    val new : unit -> state
    val write : state * Word64.word -> state
    val finalize : state -> Word64.word
  end = struct
    type state = {
      v0: Word64.word,
      v1: Word64.word,
      v2: Word64.word,
      v3: Word64.word
    }
    fun rotl (x, b) = Word64.orb (Word64.<< (x, b), Word64.>> (x, 0w64 - b))
    fun compress ({v0, v1, v2, v3}: state) =
      let val v0 = v0 + v1
            val v1 = rotl (v1, 0w13)
            val v1 = Word64.xorb (v1, v0)

          val v0 = rotl (v0, 0w32)

          val v2 = v2 + v3
            val v3 = rotl (v3, 0w16)
            val v3 = Word64.xorb (v3, v2)

          val v0 = v0 + v3
            val v3 = rotl (v3, 0w21)
            val v3 = Word64.xorb (v3, v0)

          val v2 = v2 + v1
            val v1 = rotl (v1, 0w17)
            val v1 = Word64.xorb (v1, v2)

          val v2 = rotl (v2, 0w32)
      in  {v0=v0, v1=v1, v2=v2, v3=v3}
      end
      fun cRounds state = compress state
      fun dRounds state = compress (compress (compress state))
      fun finalize ({v0, v1, v2, v3}: state) =
        let val v2 = Word64.xorb (v2, 0wxff)
            val {v0, v1, v2, v3} = dRounds {v0=v0, v1=v1, v2=v2, v3=v3}
        in  Word64.xorb (Word64.xorb (Word64.xorb (v0, v1), v2), v3)
        end
      fun new () : state =
        let val v0 = 0wx736f6d6570736575
            val v1 = 0wx646f72616e646f6d
            val v2 = 0wx6c7967656e657261
            val v3 = 0wx7465646279746573
        in  {v0=v0, v1=v1, v2=v2, v3=v3}
        end

      fun write ({v0, v1, v2, v3}: state, x: Word64.word) =
        let val v3 = Word64.xorb (v3, x)
            val {v0, v1, v2, v3} = cRounds {v0=v0, v1=v1, v2=v2, v3=v3}
        in  {v0=Word64.xorb (v0, x), v1=v1, v2=v2, v3=v3}
        end
  end

  fun hashMix (x: word) =
    let val state = SipHash13.new ()
        val state = SipHash13.write (state, Word.toLarge x)
    in  Word.fromLarge (SipHash13.finalize state)
    end

  fun hashCombine (hash1: word, hash2: word) =
    let val state = SipHash13.new ()
        val state = SipHash13.write (state, Word.toLarge hash1)
        val state = SipHash13.write (state, Word.toLarge hash2)
    in  Word.fromLarge (SipHash13.finalize state)
    end

  (* TODO: Feature request *)
  (* C++ Boost's hash_combine *)
  fun hashMix x =
    let val m1 = 0wx21f0aaad
        val m2 = 0wx735a2d97
        val x  = Word.xorb (x, Word.>> (x, 0w16))
        val x  = x * m1
        val x  = Word.xorb (x, Word.>> (x, 0w15))
        val x  = x * m2
        val x  = Word.xorb (x, Word.>> (x, 0w15))
    in  x
    end

  fun hashCombine (hash1, hash2) =
    hashMix (hash1 + 0wx9e3779b9 + hash2)

  structure LV = struct
    open LambdaVar
    structure MonoSet = HashSetFn(struct
      open Tbl.Key
      (* val hashVal = hashMix o Word.fromInt o toId *)
    end)
  end

  type lvar = LV.lvar
  type functions = { known: LabelledCPS.function list, unknown: bool }
  type variables = { known: LabelledCPS.lvar list, escape: bool }
  type result = {
    lookup: LambdaVar.lvar -> functions option,
    flow  : LabelledCPS.function -> variables
  }

  structure Value :> sig
    datatype t = Function of LCPS.function
               | Record   of int * lvar
               | Mutable  of lvar
               | Value    of LCPS.cty (* TODO: flatten *)

    val hash : t -> word
    val same : t * t -> bool
    val toString : t -> string

    structure HashSet : MONO_HASH_SET where type Key.hash_key = t
  end = struct
    datatype t = Function of LCPS.function
               | Record   of int * lvar
               | Mutable  of lvar
               | Value    of LCPS.cty

    fun hash v =
      let val funtag = 0w0
          val rectag = 0w1
          val muttag = 0w2
          val valtag = 0w3
          val hashvar = Word.fromInt o LV.toId
          fun hashTy (CPS.NUMt _) = 0w0
            | hashTy (CPS.PTRt _) = 0w1
            | hashTy (CPS.FUNt)   = 0w2
            | hashTy (CPS.FLTt _) = 0w3
            | hashTy (CPS.CNTt)   = 0w4
      in  case v
            of Function f => hashMix (hashvar (#2 f))
             | Record (i, v) => hashCombine (Word.fromInt i, hashvar v)
             | Mutable v => hashMix (hashvar v)
             | Value ty => hashMix (hashTy ty)
      end

    fun hash v =
      let val funtag = 0w0
          val rectag = 0w1
          val muttag = 0w2
          val valtag = 0w3
          val hashvar = Word.fromInt o LV.toId
          fun hashTy (CPS.NUMt _) = 0w0
            | hashTy (CPS.PTRt _) = 0w1
            | hashTy (CPS.FUNt)   = 0w2
            | hashTy (CPS.FLTt _) = 0w3
            | hashTy (CPS.CNTt)   = 0w4
      in  case v
            of Function f => hashCombine (funtag, hashvar (#2 f))
             | Record (i, v) => hashCombine (Word.fromInt i, hashvar v)
             | Mutable v => hashCombine (muttag, hashvar v)
             | Value ty => hashCombine (valtag, hashTy ty)
      end

    fun same (Function f1, Function f2) = LV.same (#2 f1, #2 f2)
      | same (Record (i1, v1), Record (i2, v2)) =
          i1 = i2 andalso LV.same (v1, v2)
      | same (Mutable v1, Mutable v2) = LV.same (v1, v2)
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
      | toString (Record (i, v)) =
          concat ["{.", Int.toString i, " = ", LV.lvarName v, "} [R]"]
      | toString (Mutable v) = concat [LV.lvarName v, "[REF]"]
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

    structure Priority : PRIORITY where type item = t

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

    structure Priority : PRIORITY = struct
      type priority = int
      val compare = Int.compare
      type item = t
      fun priority (x >-> y) = 1
        | priority (v --> y) = 3
        | priority (/-- f) = 2
        | priority (--/ v) = 4
    end
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
    val merge          : t -> lvar * lvar -> (Value.t -> unit) -> unit
    val forallValuesOf : t -> lvar -> (Value.t -> unit) -> unit
    val transitivity   : t -> Value.t * lvar -> (Fact.t -> unit) -> unit
    val lookup : t -> lvar -> functions option
    val getFlow : t -> LCPS.function -> variables
    val dump : t -> unit
    val dumpFlowGraph : t -> unit
    val dumpClosureDependency : Syn.t * t -> unit
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
      sink  = LV.MonoSet.mkEmpty (hint div 5),
      escape = LCPS.FunMonoSet.mkEmpty (hint div 5)
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

    (* TODO: Try uncurrying this *)
    fun forallValuesOf ({store, ...}: t) v f =
      (case LVT.find store v
         of SOME set => VS.app f set
          | NONE => ())

    fun merge ({store, ...}: t) (src, dst) f =
      let val facts1' = LVT.find store src
          val facts2' = LVT.find store dst
      in  case (facts1', facts2')
            of (NONE, _) => ()
             | (SOME facts1, NONE) =>
                 let val facts2 = VS.copy facts1
                     val () = LVT.insert store (dst, facts2)
                     val () = VS.app f facts2
                 in  ()
                 end
             | (SOME facts1, SOME facts2) =>
                 let fun insert (fact, diff) =
                       if VS.member (facts2, fact) then
                         diff
                       else
                         (VS.add (facts2, fact); fact :: diff)
                     val diff = VS.fold insert [] facts1
                     val () = app f diff
                 in  ()
                 end
      end

    fun transitivity (t as {row, ...}: t) (v, x) f =
      (case LVT.find row x
         of SOME set =>
              LVS.app (fn y => if add t (v --> y) then f (v --> y) else ()) set
          | NONE => ())

    fun lookup ({store, ...}: t) v =
      (case LVT.find store v
         of NONE => NONE
          | SOME set =>
              let fun collect (Function f, {known, unknown}) =
                        {known=f::known, unknown=unknown}
                    | collect (Record _, acc) = acc
                    | collect (Mutable _, acc) = acc
                    | collect (Value (CPS.FUNt | CPS.CNTt), {known, unknown}) =
                        {known=known, unknown=true}
                    | collect (Value _, acc) = acc
              in  case VS.fold collect {known=[], unknown=false} set
                    of {known=[], unknown=false} => NONE
                     | result => SOME result
              end)
    fun getFlow ({escape, row, ...}: t) f =
      let val name = #2 f
          val escape = LCPS.FunMonoSet.member (escape, f)
      in  case LVT.find row name
            of NONE => { known=[name], escape=escape }
             | SOME set => { known=name :: LVS.toList set, escape=escape }
      end

    fun histogram (xs: int list) =
      let fun insert (x, map) =
            (case IntRedBlackMap.find (map, x)
               of SOME n => IntRedBlackMap.insert (map, x, n + 1)
                | NONE   => IntRedBlackMap.insert (map, x, 1))
          fun show (n, count, ()) =
            app print [Int.toString n, " | ", Int.toString count, "\n"]
          val hist = foldl insert IntRedBlackMap.empty xs
      in  IntRedBlackMap.foldli show () hist
      end

    fun dump ({row, store, sink, escape}: t) =
      let val puts = print o concat
          fun prow (x, set) =
            puts [LV.lvarName x, " >-> {",
                  String.concatWithMap " " LV.lvarName (LVS.listItems set),
                  Int.toString (LVS.numItems set),
                  "}\n"]
          fun pstore (x, vs) =
            puts [LV.lvarName x, " <-- {",
                  (* String.concatWithMap " " Value.toString (VS.listItems vs), *)
                  Int.toString (VS.numItems vs),
                  "}\n"]
          fun valueSetTally set =
            let fun v (Function _, ls) = 0 :: ls
                  | v (Record _, ls) = 1 :: ls
                  | v (Mutable _, ls) = 2 :: ls
                  | v (Value _, ls) = 3 :: ls
                (* fun v (fact, ls) = Word.toInt (Value.hash fact mod 0w64) :: ls *)
            in  VS.fold v [] set
            end
          fun rowSizes (x, set, data) = LVS.bucketSizes set @ data
          fun storeSizes (x, set, data) = VS.bucketSizes set @ data
          fun storeSizes (x, set, data) = valueSetTally set @ data
          val () = histogram (LVT.foldi rowSizes [] row)
          val () = print "-----------------------------------------\n"
          val () = histogram (LVT.foldi storeSizes [] store)
      in
          (* LVT.appi prow row; *)
          (* LVT.appi pstore store; *)
          (* puts ["/-- {", *)
          (*       String.concatWithMap " " (LV.lvarName o #2) *)
          (*       (LCPS.FunMonoSet.listItems escape), *)
          (*       "}\n"]; *)
          (* puts ["--/ {", *)
          (*       String.concatWithMap " " LV.lvarName (LVS.listItems sink), *)
          (*       "}\n"] *)
          ()
      end

    local open DotLanguage in
    fun dumpFlowGraph ({row, store, sink, escape}) =
      let val dot = empty (true, "flow-graph")
          val functions = LCPS.FunMonoSet.mkEmpty 32
          fun collectFunctions values =
            let fun chk (Function f) = LCPS.FunMonoSet.add (functions, f)
                  | chk _ = ()
            in  VS.app chk values
            end
          val () = LVT.app collectFunctions store
          fun fromF f =
            let val name = LV.lvarName (#2 f)
                val fname = "[F]" ^ name
                val node =
                  if LCPS.FunMonoSet.member (escape, f) then
                    NODE (name, [("label", fname), ("color", "red")])
                  else
                    NODE (name, [("label", fname)])
            in  [node]
            end
          fun fromV v =
            if LVS.member (sink, v) then
              NODE (LV.lvarName v, [("color", "red")])
            else
              NODE (LV.lvarName v, [])
          fun reachable functions =
            let val set = LVS.mkEmpty 32
                fun dfs n =
                  if LVS.member (set, n) then
                    ()
                  else
                    (LVS.add (set, n);
                     (case LVT.find row n
                        of SOME ys => LVS.app dfs ys
                         | NONE => ()))
            in  LCPS.FunMonoSet.app (fn f => dfs (#2 f)) functions;
                set
            end
          val reachableVs = reachable functions
          fun prow (x, set, dot) =
            let fun collect (y, edges) =
                  (EDGE (LV.lvarName x, LV.lvarName y, []) :: edges)
            in  if LVS.member (reachableVs, x) then
                  <+< (dot, LVS.fold collect [] set)
                else
                  dot
            end
          fun run dot =
            let
                val dot =
                  LCPS.FunMonoSet.fold (fn (f, d) => <+< (d, fromF f))
                    dot functions
                val dot =
                  LVS.fold (fn (v, d) =>
                    if LVS.member (reachableVs, v) then
                      << (d, fromV v)
                    else d) dot sink
                val dot = LVT.foldi prow dot row
            in  dot
            end
      in  dump (run (<+< (dot, [ATTR "rankdir=\"LR\"", ATTR "rank=source"])))
      end
    fun dumpClosureDependency (syn, {row, store, sink, escape}) =
      let val dot = empty (true, "dependency-graph")
          val functions = LCPS.FunMonoSet.mkEmpty 32
          fun collectFunctions values =
            let fun chk (Function f) = LCPS.FunMonoSet.add (functions, f)
                  | chk _ = ()
            in  VS.app chk values
            end
          val () = LVT.app collectFunctions store
          fun fromF (f, fv) =
            let val name = LV.lvarName (#2 f)
                val closure =
                  concat ["Closure ", name, "<", String.concatWithMap ", "
                             LV.lvarName (LV.Set.listItems fv), ">"]
                val node =
                  if LCPS.FunMonoSet.member (escape, f) then
                    NODE (name, [("label", closure), ("color", "red")])
                  else
                    NODE (name, [("label", closure)])
            in  node
            end
          fun fromV v =
            if LVS.member (sink, v) then
              NODE (LV.lvarName v, [("color", "red")])
            else
              NODE (LV.lvarName v, [])
          fun pf (function as (_, name, _, _, _), dot) =
            let val fv = LV.Set.subtract (Syn.fv syn function, name)
                val self = fromF (function, fv)
                fun dofv (v, dot) =
                  (case LVT.find store v
                     of SOME values =>
                          let val fs = VS.fold
                            (fn (Function f, acc) => f :: acc
                              | (_, acc) => acc) [] values
                          in  case fs
                                of [] => dot
                                 | _ =>
                                     <+< (dot, fromV v ::
                                               EDGE (LV.lvarName v, LV.lvarName
                                               name, []) ::
                                       foldl (fn (f, edges) =>
                                         if LV.same (#2 f, v) then edges
                                         else
                                         (EDGE (LV.lvarName (#2 f),
                                                LV.lvarName v,
                                                [("style", "dotted")]) :: edges))
                                         [] fs)
                          end
                      | NONE => dot)
            in  LV.Set.foldl dofv (<< (dot, self)) fv
            end

          fun run dot =
            let val dot = LCPS.FunMonoSet.fold pf dot functions
            in  dot
            end
      in  dump (run (<+< (dot, [ATTR "rankdir=\"LR\"", ATTR "rank=source"])))
      end
    end
  end

  structure Profiler :> sig
    type timer

    val fvo : timer
    val fuo : timer
    val trans : timer
    val member : timer
    val remember : timer
    val propa : timer

    val profile : timer -> ('a -> 'b) -> ('a -> 'b)
    val report  : unit -> unit

  end = struct
    type timer = Time.time ref

    fun profile timer f a =
      let
        val start = Time.now ()
        val result = f a
        val stop = Time.now ()
        val diff = Time.- (stop, start)
        val () = timer := Time.+ (!timer, diff)
      in
        result
      end

    val fvo = ref Time.zeroTime
    val fuo = ref Time.zeroTime
    val trans = ref Time.zeroTime
    val member = ref Time.zeroTime
    val remember = ref Time.zeroTime
    val propa = ref Time.zeroTime

    fun report () =
      let val puts = app print
          val () = puts ["fvo :", Time.toString (!fvo), "\n"]
          val () = puts ["fuo :", Time.toString (!fuo), "\n"]
          val () = puts ["trans :", Time.toString (!trans), "\n"]
          val () = puts ["member :", Time.toString (!member), "\n"]
          val () = puts ["remember :", Time.toString (!remember), "\n"]
          val () = puts ["propa :", Time.toString (!propa), "\n"]
      in  ()
      end
  end

  structure PQueue = LeftPriorityQFn(Fact.Priority)

  structure Context :> sig
    type ctx
    val mk : Syn.t -> ctx
    val remember : ctx * Fact.t -> unit
    val next : ctx -> Fact.t option
    val dump : ctx -> unit
    val forallValuesOf : ctx -> lvar -> (Value.t -> unit) -> unit
    val merge : ctx -> lvar * lvar -> unit
    val forallUsesOf   : ctx -> lvar -> (LCPS.cexp -> unit) -> unit
    val transitivity   : ctx -> Value.t * lvar -> unit
    val member : ctx -> Fact.t -> bool
    val result : ctx -> result
    val dumpFlowGraph : ctx -> unit
    val dumpClosureDependency : ctx -> unit
    (* val summary : ctx -> unit *)
  end = struct
    type ctx = {
      todo  : PQueue.queue ref,
      facts : FactSet.t,
      syn   : Syn.t
    }

    fun mk syn = {
      todo=ref PQueue.empty,
      facts=FactSet.mk (Syn.numVars syn),
      syn=syn
    }

    fun next ({todo, ...}: ctx) =
      (case PQueue.next (!todo)
         of NONE => NONE
          | SOME (item, queue) => (todo := queue; SOME item))

    fun enqueue (todo, fact) =
      todo := PQueue.insert (fact, !todo)

    fun remember ({todo, facts, ...}: ctx, fact) =
      if FactSet.add facts fact then enqueue (todo, fact) else ()

    fun forallUsesOf ({syn, ...}: ctx) x f =
      let val set = Syn.usePoints syn x
      in  LCPS.Set.app f set
      end

    fun merge ({facts, todo, ...}: ctx) (src, dst) =
      FactSet.merge facts (src, dst) (fn v => enqueue (todo, v --> dst))

    fun forallUsesOf' ctx x f =
      Profiler.profile Profiler.fuo (forallUsesOf ctx x) f

    fun forallValuesOf ({facts, ...}: ctx) = FactSet.forallValuesOf facts

    fun forallValuesOf' ctx x f =
      Profiler.profile Profiler.fvo (forallValuesOf ctx x) f

    fun transitivity ({facts, todo, ...}: ctx) (v, x) =
      FactSet.transitivity facts (v, x) (fn f => enqueue (todo, f))

    fun transitivity' ctx vx =
      Profiler.profile Profiler.trans (transitivity ctx) vx

    fun member ({facts, ...}: ctx) f = FactSet.member facts f

    fun member' ctx f = Profiler.profile Profiler.member (member ctx) f

    fun dump {todo, facts, syn=_} =
      (print "Context:\n";
       FactSet.dump facts;
       ())

    fun result ({facts, ...}: ctx) =
      { lookup=FactSet.lookup facts, flow=FactSet.getFlow facts }

    fun dumpFlowGraph ({facts, ...}: ctx) = FactSet.dumpFlowGraph facts
    fun dumpClosureDependency ({facts, syn, ...}: ctx) =
      FactSet.dumpClosureDependency (syn, facts)

    (* fun summary ({facts, ...}: ctx) = *)
    (*   (print "Escaping: {"; *)
    (*    Fact.HashSet.app (fn (/-- f) => print (LV.lvarName (#2 f) ^ ", ") *)
    (*                       | _ => ()) facts; *)
    (*    print "}\n") *)
  end

  fun label _ = raise Impossible "Label generated before closure conversion"
  fun offset _ = raise Impossible "Offset"
  val bogusTy = CPSUtil.BOGt

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

  fun fromType (v, ty) = Value ty --> v

  fun fieldOf (fields : (lvar * CPS.value * CPS.accesspath) list, v) : int * lvar =
    let fun check (_, CPS.VAR w, CPS.OFFp 0) = LV.same (v, w)
          | check (_, CPS.VAR _, _) = offset ()
          | check (_, _, _) = false
    in  case List.findi (check o #2) fields
          of SOME (i, _) => (i, v)
           | NONE => raise Impossible "bug: indexOf not found"
    end

  fun initialize (syn, cps) =
    let
      val ctx = Context.mk syn
      fun add fact = Context.remember (ctx, fact)
      (* FIXME: If functions flow to GETVAR *)
      fun walkB (f as (kind, name, args, tys, body)) =
            (add (Function f --> name); walk body)
      and walk (RECORD (label, CPS.RK_VECTOR, values, dest, cexp)) = walk cexp
        | walk (RECORD (_, _, values, dest, cexp)) = walk cexp
        | walk (SELECT (_, _, _, _, _, cexp)) = walk cexp
        | walk (OFFSET _) = offset ()
        | walk (APP _) = ()
        | walk (FIX (_, bindings, cexp)) = (app walkB bindings; walk cexp)
        | walk (SWITCH (_, _, _, branches)) = app walk branches
        | walk (BRANCH (_, _, _, _, te, fe)) = (walk te; walk fe)
        | walk (SETTER (_, _, _, cexp)) = walk cexp
        | walk (LOOKER (_, CPS.P.GETHDLR, _, dest, _, cexp)) =
            (add (Value CPS.FUNt --> dest); walk cexp)
        | walk (LOOKER (_, _, _, _, _, cexp)) = walk cexp
        | walk (ARITH (_, _, _, dest, ty, cexp)) =
            (add (Value ty --> dest); walk cexp)
        | walk (PURE (label, CPS.P.MAKEREF, values, dest, _, cexp)) =
                walk cexp
        | walk (PURE (label, (CPS.P.RAWRECORD _ | CPS.P.NEWARRAY0), _,
                      dest, _, cexp)) =
            (* (add (Mutable label --> dest); *)
            (* FIXME: check this case *)
             walk cexp
             (* ) *)
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
      val merge = Context.merge ctx

      fun propagate (/-- (function as (kind, name, args, tys, body))) =
            (ListPair.appEq (add o fromType) (args, tys))
        | propagate (x >-> y) = merge (x, y)
            (* forallValuesOf x (fn v => add (v --> y)) *)
        | propagate (--/ x) = forallValuesOf x escape
        | propagate (v --> x) =
            (if member (--/ x) then escape v else ();
             transitivity (v, x);
             propagateValue (v, x))
      and propagateValue (Function (func as (_, _, formals, _, _)), x) =
            forallUsesOf x
              (fn APP (_, f, args) =>
                    if LV.same (x, varOf f) then
                      ListPair.appEq (add o flowValue) (args, formals)
                    else ()
                | SETTER (_, CPS.P.SETHDLR, _, _) => add (/-- func)
                | cexp => record (cexp, x))
        | propagateValue (Value (CPS.FUNt|CPS.CNTt), x) =
            forallUsesOf x
              (fn APP (_, f, args) =>
                    let fun markEscape (CPS.VAR v) = add (--/ v)
                          | markEscape _ = ()
                    in  if LV.same (x, varOf f) then
                          List.app markEscape args
                        else ()
                    end
                | cexp => record (cexp, x))
        | propagateValue (Record (i', v), x) =
            forallUsesOf x
              (fn SELECT (_, i, _, dest, _, _) =>
                    if i = i' then add (v >-> dest) else ()
                | cexp => record (cexp, x))
        | propagateValue (Mutable r, x) =
            forallUsesOf x
              (* TODO: ignore unboxed assign, handle update *)
              (fn SETTER (_, (CPS.P.ASSIGN|CPS.P.UNBOXEDASSIGN), args, _) =>
                    let val (_, rhs) = twoArgs args
                    in  add (flowValue (rhs, r))
                    end
                | LOOKER (_, (CPS.P.DEREF|CPS.P.SUBSCRIPT), _, dest, _, _) =>
                    add (r >-> dest)
                | cexp => record (cexp, x))
        | propagateValue (Value ty, x) =
            forallUsesOf x
              (fn SELECT (_, _, value, dest, ty, _) =>
                    add (fromType (dest, ty))
                | APP (_, f, args) =>
                    () (* Uniform value cannot be used as a function *)
                | LOOKER (_, _, _, dest, ty, _) =>
                    add (fromType (dest, ty))

                (* If a cell contains an unknown value, i.e., makeref(x),
                 * we don't need to create a cell unless x can contain a
                 * function. That is, x has type FUNt, CNTt, or PTRt. The
                 * former two cases has been handled by the above, so we
                 * just need to handle the case of PTRt. *)

                | RECORD (_, _, fields, dest, _) =>
                    add (Value bogusTy --> dest)
                | PURE   (_, _, _, dest, ty, _) =>
                    add (fromType (dest, ty))
                | _ => ())
      and escape (Function f) = add (/-- f)
        | escape (Record (_, v)) =
              if not (member (--/ v)) then
                (add (--/ v); forallValuesOf v escape)
              else ()
        | escape (Mutable v) =
              if not (member (--/ v)) then
                (add (--/ v);
                 transitivity (Value CPS.FUNt, v);
                 forallValuesOf v escape)
              else ()
        | escape (Value _) = ()
      and record (cexp, x) =
            (case cexp
               of RECORD (label, CPS.RK_VECTOR, fields, dest, _) =>
                    (add (Mutable label --> dest); add (x >-> label))
                | RECORD (_, _, fields, dest, _) =>
                    add (Record (fieldOf (fields, x)) --> dest)
                | PURE   (label, CPS.P.MAKEREF, values, dest, _, _) =>
                    (add (Mutable label --> dest); add (x >-> label))
                | PURE   (label, CPS.P.CAST, values, dest, _, _) =>
                    (add (x >-> dest))
                | _ => (* These are all constructors by which a function can end
                        * up in a data structure *)
                    ())

      fun dump n = (print ("\r" ^ Int.toString n))
      fun dump _ = ()
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
        val () = timeit "flow-cfa " (fn () => run ctx)
        (* val () = Context.dumpFlowGraph ctx *)
        val () = Context.dump ctx
      (* val () = Profiler.report () *)
        (* val () = Context.dumpClosureDependency ctx *)
    in  Context.result ctx
    end
end
