structure ZeroCFA :> CFA = struct
  structure CallGraph = CallGraph
  structure LCPS = LabelledCPS

  structure Value :> sig
    datatype concrete
      = FUN    of LCPS.function
      | RECORD of addr list
      | ARRAY  of addr list
      | DATA (* data is everything that cannot contain functions *)
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
    val arrays: t -> (addr list) list option
    val functions: t -> (LCPS.function) list option

    val recordsL: concrete list -> (addr list) list option
    val arraysL: concrete list -> (addr list) list option
    val functionsL: concrete list -> (LCPS.function) list option
  end = struct
    datatype concrete
      = FUN    of LCPS.function
      | RECORD of addr list
      | ARRAY  of addr list
      | DATA
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
        | sameKey (ARRAY a, ARRAY b) =
            ListPair.allEq sameAddr (a, b)
        | sameKey (DATA, DATA) = true
        | sameKey (T, T) = true
        | sameKey _ = false

      fun hashVal v =
        let
          val dataTag   = 0w0
          val funTag    = 0w1
          val recordTag = 0w2
          val arrayTag  = 0w3
          val topTag    = 0w4
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
             | ARRAY addrs =>
                 addTag (foldl (fn (v, h) => hashCombine (h, hashAddr v))
                               0w0
                               addrs,
                         arrayTag)
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
        (Set.add (set, v); true)

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
      | dumpC (ARRAY addrs) =
          (say "{";
           say (String.concatWithMap ", " LambdaVar.lvarName addrs);
           say "} [A]")
      | dumpC DATA =
          say "[D]"
      | dumpC T =
          say "[TOP]"

    fun isTop set = Set.member (set, T)
    fun dump set = (say "["; Set.app (fn c => (dumpC c; say ",")) set; say "]")

    val records = collect (fn (RECORD data) => SOME data | _ => NONE) Set.fold
    val arrays = collect (fn (ARRAY data) => SOME data | _ => NONE) Set.fold
    val functions = collect (fn (FUN data) => SOME data | _ => NONE) Set.fold

    val recordsL = collect (fn (RECORD data) => SOME data | _ => NONE) List.foldl
    val arraysL = collect (fn (ARRAY data) => SOME data | _ => NONE) List.foldl
    val functionsL = collect (fn (FUN data) => SOME data | _ => NONE) List.foldl
  end

  structure Store :> sig
    type t
    val new: unit -> t

    val epoch: t -> int
    val update: t -> CPS.lvar * Value.concrete -> bool
    val setTop: t -> CPS.lvar -> bool
    val merge: t -> CPS.lvar * Value.t -> bool
    val lookup: t -> CPS.lvar -> Value.t
    val dump: t -> unit
  end = struct
    structure LVarTbl = LambdaVar.Tbl

    type t = {epoch: int ref, table: Value.t LVarTbl.hash_table}

    exception StoreLookUp
    fun new () = {epoch=ref 0, table=LVarTbl.mkTable (32, StoreLookUp)}

    fun epoch ({epoch, ...}: t) = !epoch

    fun updateEpoch epoch true  = (epoch := !epoch + 1; true)
      | updateEpoch epoch false = false

    fun update {epoch, table} (lvar, v) =
      case LVarTbl.find table lvar
        of SOME set => updateEpoch epoch (Value.add (set, v))
         | NONE => (LVarTbl.insert table (lvar, Value.mk v);
                    updateEpoch epoch true)

    fun setTop {epoch, table} lvar =
      case LVarTbl.find table lvar
        of SOME set => updateEpoch epoch (Value.setTop set)
         | NONE => (LVarTbl.insert table (lvar, Value.mk Value.T);
                    updateEpoch epoch true)

    fun merge {epoch, table} (lvar, value) =
      case LVarTbl.find table lvar
        of SOME orig => updateEpoch epoch (Value.merge (orig, value))
         | NONE => (LVarTbl.insert table (lvar, Value.copy value);
                    updateEpoch epoch true)

    val say = print

    fun dump {epoch, table} =
      (say "epoch: "; say (Int.toString (!epoch)); say "\n";
       LVarTbl.appi (fn (k, v) => (say (LambdaVar.lvarName k);
                                   say " ---> ";
                                   Value.dump v;
                                   say "\n"))
                    table)

    fun lookup (s as {table, ...}: t) lvar = LVarTbl.lookup table lvar
      handle StoreLookUp => (say "LOOKUP FAIL: ";
                             say (LambdaVar.lvarName lvar);
                             say "\n";
                             dump s;
                             raise StoreLookUp)
  end

  exception Unimp
  exception Impossible of string
  fun analyze (fun_kind, name, formals, tys, body) =
    let
      exception EpochLookUp
      val epochTable = LCPS.Tbl.mkTable (1024, EpochLookUp)
      val store = Store.new ()

      fun fetchEpoch cexp =
        case LCPS.Tbl.find epochTable cexp
          of SOME epoch => epoch
           | NONE => (LCPS.Tbl.insert epochTable (cexp, ~1); ~1)

      fun evalVar v = Store.lookup store v

      fun evalValue (CPS.VAR v) =
            evalVar v
        | evalValue (CPS.LABEL _) =
            raise (Impossible "Label value before closure conversion")
        | evalValue _ =
            Value.mk Value.DATA

      fun access (concretes, CPS.OFFp 0) = concretes
        | access (concretes, CPS.OFFp i) =
            let
              fun offset addrs = SOME (Value.RECORD (List.drop (addrs, i)))
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
                   val values = Value.toList (Store.lookup store addr)
                 in
                   access (values, p)
                 end)
                handle Subscript => []
            in
              case Value.recordsL concretes
                of SOME candidates => List.concatMap get candidates
                 | NONE => [Value.T]
            end

      fun allocValue (dest, src, path) =
        let
          val concretes = access (Value.toList (evalValue src), path)
          val value = Value.from concretes
        in
          Store.merge store (dest, value); dest
        end

      fun dump cexp =
        (print "Current expression:\n";
         PPCps.prcps (LCPS.unlabel cexp);
         print "\nCurrent state:\n";
         Store.dump store;
         print "=================\n\n\n")

      fun go cexp =
        let
          val lastEpoch = fetchEpoch cexp
          val currEpoch = Store.epoch store
        in
          if currEpoch <= lastEpoch then
            ()
          else
            (LCPS.Tbl.insert epochTable (cexp, currEpoch);
             dump cexp;
             case cexp
               of LCPS.APP (_, f, args) =>
                    let
                      val argVals = map evalValue args
                      fun call (Value.FUN (_, name, formals, types, body)) =
                            ((app (ignore o Store.merge store)
                                 (ListPair.zipEq (formals, argVals));
                              go body)
                             handle ListPair.UnequalLengths => ())
                            (* if the function is applied with incorrect number
                             * of arguments, this path is aborted *)
                         | call Value.T = ()
                            (* FIXME: escape *)
                         | call _ = ()
                            (* if applying a non-function, nothing to be done *)
                    in
                      Value.app call (evalValue f)
                    end
                | LCPS.RECORD (_, _, values, x, body) =>
                    let
                      val record = Value.RECORD (map allocValue values)
                    in
                      Store.update store (x, record);
                      go body
                    end
                | LCPS.SELECT (_, i, value, dest, _, body) =>
                    let
                      val values =
                        case Value.records (evalValue value)
                          of SOME records =>
                               List.mapPartial
                                 (fn addrs => SOME (Store.lookup store
                                                      (List.nth (addrs, i)))
                                              handle Subscript => NONE)
                                 records
                           | NONE => [Value.mk Value.T]
                    in
                      app (fn v => (Store.merge store (dest, v); ())) values;
                      go body
                    end
                | LCPS.OFFSET (_, i, value, dest, body) =>
                    let
                      val v =
                        case Value.records (evalValue value)
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
                      Store.merge store (dest, v);
                      go body
                    end
                | LCPS.FIX (_, bindings, body) =>
                    let
                      fun bind (f as (_, name, _, _, _)) =
                        ignore (Store.update store (name, Value.FUN f))
                    in
                      app bind bindings;
                      go body
                    end
                | LCPS.SWITCH (_, _, _, arms) =>
                    (* Since we are not tracking integers, visit all arms *)
                    app go arms
                | LCPS.BRANCH (_, _, _, _, trueExp, falseExp) =>
                    (go trueExp; go falseExp)
                | LCPS.SETTER (_, _, _, body) =>
                    (* TODO: Array/Ref support; should have some marker of
                     * escaping function here *)
                    go body
                | LCPS.LOOKER (_, _, _, dest, _, body) =>
                    raise Impossible "Oh no LOOKER"
                | LCPS.ARITH (_, _, _, dest, _, body) =>
                    (* FIXME: There is no support for exception now *)
                    (Store.update store (dest, Value.DATA); go body)
                | LCPS.PURE (_, _, _, dest, (CPS.NUMt _ | CPS.FLTt _), body) =>
                    (Store.update store (dest, Value.DATA); go body)
                | LCPS.PURE (_, _, _, dest, cty, body) =>
                    raise Impossible "Oh no PURE"
                | LCPS.RCC _ =>
                    raise Unimp
            )
        end
    in
      app (fn arg => ignore (Store.update store (arg, Value.T))) formals;
      go body;
      Store.dump store;
      raise Unimp
    end
end
