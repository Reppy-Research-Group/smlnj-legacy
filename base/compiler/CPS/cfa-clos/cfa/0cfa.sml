structure ZeroCFA :> CFA = struct
  structure CallGraph = CallGraph
  structure LCPS = LabelledCPS

  structure Value :> sig
    datatype concrete
      = FUN    of LCPS.function
      | RECORD of addr list
      | REF    of addr
      | DATA (* data is everything that cannot contain functions *)
      | UNCAUGHTEXN
      | T
    withtype addr = LCPS.lvar
    type t

    val mk: concrete -> t
    val from: concrete list -> t
    val copy: t -> t

    val add: t * concrete -> bool
    val merge: t * t -> bool
    val setTop: t -> bool

    val toList: t -> concrete list

    val dump: t -> unit

    val isTop: t -> bool
    val app: (concrete -> unit) -> t -> unit

    val records: t -> (addr list) list option
    val functions: t -> (LCPS.function) list option

    val recordsL: concrete list -> (addr list) list option
    val functionsL: concrete list -> (LCPS.function) list option
  end = struct
    datatype concrete
      = FUN    of LCPS.function
      | RECORD of addr list
      | REF    of addr
      | DATA
      | UNCAUGHTEXN
      | T
    withtype addr = LCPS.lvar

    structure Set = HashSetFn(struct
      val sameAddr = LambdaVar.same
      val hashAddr = Word.fromInt o LambdaVar.toId
      fun hashCombine (hash1, hash2) =
        (* C++ Boost's hash_combine *)
        Word.xorb (hash1, Word.+ (hash2,
                                  (Word.+ (0wx9e3779b9,
                                           (Word.+ (Word.<< (hash1, 0w6),
                                                    Word.>> (hash1, 0w2)))))))

      type hash_key = concrete
      fun sameKey (FUN (_, lvar1, _, _, _), FUN (_, lvar2, _, _, _)) =
            LambdaVar.same (lvar1, lvar2)
        | sameKey (RECORD a, RECORD b) =
            ListPair.allEq sameAddr (a, b)
        | sameKey (REF a, REF b) =
            sameAddr (a, b)
        | sameKey (DATA, DATA) = true
        | sameKey (T, T) = true
        | sameKey (UNCAUGHTEXN, UNCAUGHTEXN) = true
        | sameKey _ = false

      fun hashVal v =
        let
          val dataTag   = 0w0
          val funTag    = 0w1
          val recordTag = 0w2
          val refTag    = 0w3
          val exnTag    = 0w4
          val topTag    = 0w5
          fun addTag (hash, tag) = Word.orb (Word.<< (hash, 0w3), tag)
        in
          case v
            of DATA => dataTag
             | FUN (_, lvar, _, _, _) =>
                 addTag (Word.fromInt (LambdaVar.toId lvar), funTag)
             | RECORD addrs =>
                 addTag (foldl (fn (v, h) => hashCombine (h, hashAddr v))
                               0w0
                               addrs,
                         recordTag)
             | REF addr => addTag (Word.fromInt (LambdaVar.toId addr), refTag)
             | UNCAUGHTEXN => exnTag
             | T => topTag
        end
    end)

    type t = Set.set
    val mk = Set.mkSingleton
    val from = Set.mkFromList
    val copy = Set.copy
    val app = Set.app
    val toList = Set.toList

    fun setTop set =
      let fun erase set = app (Set.subtractc set) set
      in  if Set.member (set, T) then
            false
          else
            (erase set; Set.add (set, T); true)
      end

    fun isTop set = Set.member (set, T)

    fun add (set, v) =
      if Set.member (set, T) orelse Set.member (set, v) then
        false
      else
        case v
          of T => setTop set
           | _ => (Set.add (set, v); true)

    fun merge (set1, set2) =
      Set.fold (fn (v, changed) => add (set1, v) orelse changed) false set2

    fun collect sieve fold set =
      fold (fn (T, result) => NONE
             | (_, NONE) => NONE
             | (v, SOME result) => case sieve v
                                     of SOME data => SOME (data :: result)
                                      | NONE => SOME result)
           (SOME [])
           set

    val say = print
    val sayLvar = say o LambdaVar.lvarName

    fun dumpC (FUN (_, name, _, _, _)) =
          say (LambdaVar.lvarName name ^ "[F]")
      | dumpC (RECORD addrs) =
          (say "{";
           say (String.concatWithMap ", " LambdaVar.lvarName addrs);
           say "} [R]")
      | dumpC (REF addrs) =
          say (LambdaVar.lvarName addrs ^ "[REF]")
      | dumpC DATA =
          say "[D]"
      | dumpC UNCAUGHTEXN =
          say "[UNCAUGHT]"
      | dumpC T =
          say "[TOP]"

    fun isTop set = Set.member (set, T)
    fun dump set = (say "["; Set.app (fn c => (dumpC c; say ",")) set; say "]")

    val records = collect (fn (RECORD data) => SOME data | _ => NONE) Set.fold
    val refs = collect (fn (REF data) => SOME data | _ => NONE) Set.fold
    val functions = collect (fn (FUN data) => SOME data | _ => NONE) Set.fold

    val recordsL = collect (fn (RECORD data) => SOME data | _ => NONE) List.foldl
    val refsL = collect (fn (REF data) => SOME data | _ => NONE) List.foldl
    val functionsL = collect (fn (FUN data) => SOME data | _ => NONE) List.foldl
  end

  structure Store :> sig
    type t
    val new: unit -> t

    val epoch: t -> int
    val update: t -> CPS.lvar * Value.concrete -> bool
    val setTop: t -> CPS.lvar -> bool
    val getHdlr: t -> Value.t
    val addHdlr: t -> Value.t -> bool
    val merge: t -> CPS.lvar * Value.t -> bool
    val lookup: t -> CPS.lvar -> Value.t
    val dump: t -> unit
  end = struct
    structure LVarTbl = LambdaVar.Tbl

    type t = {epoch: int ref, table: Value.t LVarTbl.hash_table, hdlr: Value.t}

    exception StoreLookUp
    fun new () =
      { epoch=ref 0
      , table=LVarTbl.mkTable (32, StoreLookUp)
      , hdlr=Value.mk Value.UNCAUGHTEXN
      }

    fun epoch ({epoch, ...}: t) = !epoch

    fun updateEpoch epoch true  = (epoch := !epoch + 1; true)
      | updateEpoch epoch false = false

    fun update {epoch, table, hdlr=_} (lvar, v) =
      case LVarTbl.find table lvar
        of SOME set => updateEpoch epoch (Value.add (set, v))
         | NONE => (LVarTbl.insert table (lvar, Value.mk v);
                    updateEpoch epoch true)

    fun setTop {epoch, table, hdlr=_} lvar =
      case LVarTbl.find table lvar
        of SOME set => updateEpoch epoch (Value.setTop set)
         | NONE => (LVarTbl.insert table (lvar, Value.mk Value.T);
                    updateEpoch epoch true)

    fun merge {epoch, table, hdlr=_} (lvar, value) =
      case LVarTbl.find table lvar
        of SOME orig => updateEpoch epoch (Value.merge (orig, value))
         | NONE => (LVarTbl.insert table (lvar, Value.copy value);
                    updateEpoch epoch true)

    fun getHdlr ({hdlr, ...}: t) = hdlr
    fun addHdlr ({hdlr, epoch, ...}: t) v =
      updateEpoch epoch (Value.merge (hdlr, v))

    val say = print

    fun dump {epoch, table, hdlr} =
      (say "epoch: "; say (Int.toString (!epoch)); say "\n";
       LVarTbl.appi (fn (k, v) => (say (LambdaVar.lvarName k);
                                   say " ---> ";
                                   Value.dump v;
                                   say "\n"))
                    table;
       say "hdlr ---> "; Value.dump hdlr; say "\n")

    fun lookup (s as {table, ...}: t) lvar = LVarTbl.lookup table lvar
      handle StoreLookUp => (say "LOOKUP FAIL: ";
                             say (LambdaVar.lvarName lvar);
                             say "\n";
                             dump s;
                             raise StoreLookUp)
  end

  exception Unimp
  exception Impossible of string
  structure Context :> sig
    type t

    val new: unit -> t
    val guard: (t -> LCPS.cexp -> unit) -> t -> LCPS.cexp -> unit
    val lookup: t -> LCPS.lvar -> Value.t
    val add: t -> (LCPS.lvar * Value.concrete) -> bool
    val merge: t -> (LCPS.lvar * Value.t) -> bool
    val dump: t -> unit
    val escape: t -> LCPS.lvar -> unit
    val escapeSet: t -> LambdaVar.Set.set
    val getHdlr: t -> Value.t
    val addHdlr: t -> Value.t -> unit
  end = struct

    type t = { epochTable: int LCPS.Tbl.hash_table
             , store: Store.t
             , escapeSet: LambdaVar.Set.set ref
             }

    exception EpochLookUp
    fun new () =
      { epochTable = LCPS.Tbl.mkTable (1024, EpochLookUp)
      , store = Store.new ()
      , escapeSet = ref LambdaVar.Set.empty
      }

    fun getHdlr ({store, ...}: t) = Store.getHdlr store
    fun addHdlr ({store, ...}: t) v = ignore (Store.addHdlr store v)

    fun fetchEpoch epochTable cexp =
      case LCPS.Tbl.find epochTable cexp
        of SOME epoch => epoch
         | NONE => (LCPS.Tbl.insert epochTable (cexp, ~1); ~1)

    fun guard f (ctx as {epochTable, store, ...}: t) cexp =
      let
        val lastEpoch = fetchEpoch epochTable cexp
        val currEpoch = Store.epoch store
      in
        if currEpoch <= lastEpoch then
          ()
        else
          (LCPS.Tbl.insert epochTable (cexp, currEpoch);
           print ("\r" ^ Int.toString currEpoch);
           f ctx cexp)
      end

    val lookup = Store.lookup o (fn (ctx: t) => #store ctx)
    val add = Store.update o (fn (ctx: t) => #store ctx)
    val merge = Store.merge o (fn (ctx: t) => #store ctx)
    fun dump {epochTable, store, escapeSet} =
      (Store.dump store;
       print "\nEscaping: {";
       LambdaVar.Set.app (fn x => print (LambdaVar.lvarName x ^ ","))
                         (!escapeSet);
       print "}")
    (* FIXME: names don't escape; functions do *)
    fun escape (ctx: t) name =
      let val setRef = #escapeSet ctx
      in  setRef := LambdaVar.Set.add (!setRef, name)
      end

    fun escapeSet ({escapeSet, ...}: t) = !escapeSet
  end

  fun evalValue ctx (CPS.VAR v) =
        Context.lookup ctx v
    | evalValue ctx (CPS.LABEL _) =
        raise (Impossible "Label value before closure conversion")
    | evalValue _ CPS.VOID =
        Value.mk Value.T
    | evalValue _ _ =
        Value.mk Value.DATA

  fun dump ctx cexp =
    (print "Current expression:\n";
     PPCps.prcps (LCPS.unlabel cexp);
     print "\nCurrent state:\n";
     Context.dump ctx;
     print "=================\n\n\n")

  fun loopExp ctx cexp = Context.guard loopExpCase ctx cexp
  and loopExpCase ctx (LCPS.APP (_, f, args)) =
        apply ctx (evalValue ctx f, args)
    | loopExpCase ctx (LCPS.RECORD (_, _, values, x, body)) =
        let
          fun access (concretes, CPS.OFFp 0) = concretes
            | access (concretes, CPS.OFFp i) =
                let
                  fun offset addrs =
                    SOME (Value.RECORD (List.drop (addrs, i)))
                    handle Subscript => NONE
                in
                  case Value.recordsL concretes
                    of SOME candidates => List.mapPartial offset candidates
                     | NONE => [Value.T]
                end
            | access (concretes, CPS.SELp (i, p)) =
                let
                  fun get addrs =
                    (let
                       val addr = List.nth (addrs, i)
                       val values = Value.toList (Context.lookup ctx addr)
                     in
                       access (values, p)
                     end)
                    handle Subscript => []
                in
                  case Value.recordsL concretes
                    of SOME candidates => List.concatMap get candidates
                     | NONE => [Value.T]
                end

          fun alloc (dest, src, path) =
            let
              val concretes = access (Value.toList (evalValue ctx src), path)
              val value = Value.from concretes
            in
              Context.merge ctx (dest, value); dest
            end

          val record = Value.RECORD (map alloc values)
        in
          Context.add ctx (x, record);
          loopExp ctx body
        end
    | loopExpCase ctx (LCPS.SELECT (_, i, value, dest, _, body)) =
        let
          val values =
            case Value.records (evalValue ctx value)
              of SOME records =>
                   List.mapPartial
                     (fn addrs => SOME (Context.lookup ctx
                                          (List.nth (addrs, i)))
                                  handle Subscript => NONE)
                     records
               | NONE => [Value.mk Value.T]
        in
          case values
            of [] => () (* no record value is accessible here; type error *)
             | _ => (app (fn v => ignore (Context.merge ctx (dest, v))) values;
                     loopExp ctx body)
        end
    | loopExpCase ctx (LCPS.OFFSET (_, i, value, dest, body)) =
        let
          val v =
            case Value.records (evalValue ctx value)
              of SOME records =>
                   let
                     fun truncate addrs =
                       SOME (Value.RECORD (List.drop (addrs, i)))
                       handle Subscript => NONE
                     val records' = List.mapPartial truncate records
                   in
                     Value.from records'
                   end
               | NONE => Value.mk Value.T
        in
          Context.merge ctx (dest, v);
          loopExp ctx body
        end
    | loopExpCase ctx (LCPS.FIX (_, bindings, body)) =
        let
          fun bind (f as (_, name, _, _, _)) =
            ignore (Context.add ctx (name, Value.FUN f))
        in
          app bind bindings;
          loopExp ctx body
        end
    | loopExpCase ctx (LCPS.SWITCH (_, _, _, arms)) =
        (* Since we are not tracking integers, visit all arms *)
        app (loopExp ctx) arms
    | loopExpCase ctx (LCPS.BRANCH (_, _, _, _, trueExp, falseExp)) =
        (loopExp ctx trueExp; loopExp ctx falseExp)
    | loopExpCase ctx (LCPS.SETTER (_, CPS.P.SETHDLR, [hdlr], body)) =
        (Context.addHdlr ctx (evalValue ctx hdlr); loopExp ctx body)
    | loopExpCase ctx (LCPS.SETTER (_, CPS.P.SETHDLR, _, _)) =
        raise Impossible "SETHDLR cannot take more than one continuation"
    | loopExpCase ctx (LCPS.SETTER (_, _, _, body)) =
        (* TODO: Array/Ref support; should have some marker of
         * escaping function here *)
        loopExp ctx body
    | loopExpCase ctx (LCPS.LOOKER (_, CPS.P.GETHDLR, [], dest, _, body)) =
        (Context.merge ctx (dest, Context.getHdlr ctx);
         loopExp ctx body)
    | loopExpCase ctx (LCPS.LOOKER (_, CPS.P.GETHDLR, _, dest, _, body)) =
        raise Impossible "GETHDLR does not take arguments"
    | loopExpCase ctx (LCPS.LOOKER (_, _, _, dest,
                                      (CPS.NUMt _ | CPS.FLTt _), body)) =
        (Context.add ctx (dest, Value.DATA); loopExp ctx body)
    | loopExpCase ctx (LCPS.LOOKER (_, _, _, dest,
                                    (CPS.FUNt | CPS.CNTt | CPS.PTRt _), body)) =
        (Context.add ctx (dest, Value.T); loopExp ctx body)
    | loopExpCase ctx (LCPS.ARITH (_, _, _, dest, _, body)) =
        (apply ctx (Context.getHdlr ctx, [CPS.VOID, CPS.VOID]);
         Context.add ctx (dest, Value.DATA);
         loopExp ctx body)
    | loopExpCase ctx (LCPS.PURE (_, _, _, dest,
                                      (CPS.NUMt _ | CPS.FLTt _), body)) =
        (Context.add ctx (dest, Value.DATA); loopExp ctx body)
    | loopExpCase ctx (LCPS.PURE (label, CPS.P.MAKEREF, [v], dest, _, body)) =
        (Context.add ctx (dest, Value.REF label);
         case v
           of CPS.VAR w => Context.merge ctx (label, Context.lookup ctx w)
            | CPS.LABEL _ => raise Impossible "label"
            | (CPS.NUM _ | CPS.REAL _ | CPS.STRING _) =>
                Context.add ctx (label, Value.DATA)
            | CPS.VOID => Context.add ctx (label, Value.T);
         loopExp ctx body)
    | loopExpCase ctx (LCPS.PURE (_, _, _, dest, _, body)) =
        (Context.add ctx (dest, Value.T); loopExp ctx body)
    | loopExpCase ctx (LCPS.RCC _) =
        raise Unimp
  and apply ctx (f: Value.t, args: LCPS.value list) =
        let
          val argVals = map (evalValue ctx) args
          fun call (Value.FUN (_, name, formals, types, body)) =
                ((app (ignore o Context.merge ctx)
                     (ListPair.zipEq (formals, argVals));
                  loopExp ctx body)
                 handle ListPair.UnequalLengths => ())
                (* if the function is applied with incorrect number
                 * of arguments, this path is aborted *)
             | call Value.T =
                 app (fn (CPS.VAR v) => Context.escape ctx v | _ => ()) args
             | call Value.UNCAUGHTEXN =
                 app (fn (CPS.VAR v) => Context.escape ctx v | _ => ()) args
             | call (Value.RECORD _ | Value.REF _ | Value.DATA) = ()
                (* if applying a non-function, nothing to be done *)
        in
          Value.app call f
        end

  fun loopEscape ctx q visited =
    let
      fun doFunction (fun_kind, name, formals, tys, body) =
        let
          val currSet = Context.escapeSet ctx
          fun enqueueValue seen (Value.FUN f) = Queue.enqueue (q, f)
            | enqueueValue seen (Value.RECORD addrs) =
                app (enqueue seen) addrs
            | enqueueValue seen (Value.REF addr) =
                enqueue seen addr
            | enqueueValue seen (Value.DATA | Value.T | Value.UNCAUGHTEXN) = ()
          and enqueue seen name =
                if LambdaVar.Set.member (seen, name) then
                  ()
                else
                  app (enqueueValue (LambdaVar.Set.add (seen, name)))
                      (Value.toList (Context.lookup ctx name))
        in
          app (fn arg => ignore (Context.add ctx (arg, Value.T))) formals;
          loopExp ctx body;
          LambdaVar.Set.app (enqueue LambdaVar.Set.empty)
            (LambdaVar.Set.difference (Context.escapeSet ctx, currSet))
        end
    in
      case Queue.next q
        of SOME (function as (_, name, _, _, _)) =>
             if LambdaVar.Set.member (visited, name) then
               loopEscape ctx q visited
             else
               (Context.escape ctx name;
                print "\nhere\n";
                doFunction function;
                print "\nhere2\n";
                loopEscape ctx q (LambdaVar.Set.add (visited, name)))
         | NONE => ()
    end

  fun analyze function =
    let
      val ctx = Context.new ()
      val queue = Queue.mkQueue ()
      val () = Queue.enqueue (queue, function)
    in
      loopEscape ctx queue LambdaVar.Set.empty;
      Context.dump ctx;
      CallGraph.new ()
    end
end
