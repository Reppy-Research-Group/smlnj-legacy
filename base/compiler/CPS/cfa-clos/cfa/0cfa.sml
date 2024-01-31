structure ZeroCFA :> CFA = struct
  structure LCPS = LabelledCPS

  structure Value :> sig
    datatype function
      = IN of LCPS.function
      | OUT
    datatype concrete
      = FUN     of function
      | RECORD  of addr list
      | REF     of addr
      | DATA                (* data is everything that is not functions *)
      | UNKNOWN of LCPS.cty
    withtype addr = LCPS.lvar
    type t

    val mk: concrete -> t
    val from: concrete list -> t
    val copy: t -> t

    val add: t * concrete -> bool
    val merge: t * t -> bool

    val toList: t -> concrete list
    val objects: t -> CallGraph.object
    val dump: t -> unit

    val app: (concrete -> unit) -> t -> unit
    (* val fold: (concrete * 'a -> 'a) -> 'a -> t -> unit *)

    (* val unknownRecords: t -> bool *)
    (* val unknownRefs: t -> bool *)

    (* val records: t -> (addr list) list *)
    (* val functions: t -> function list *)
    (* val refs: t -> addr list *)

    (* val recordsL: concrete list -> (addr list) list *)
    (* val functionsL: concrete list -> function list *)
    (* val refsL: concrete list -> addr list *)
  end = struct
    datatype function
      = IN of LCPS.function
      | OUT
    datatype concrete
      = FUN     of function
      | RECORD  of addr list
      | REF     of addr
      | DATA                (* known atomic data *)
      | UNKNOWN of LCPS.cty (* unknown data *)
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
      fun sameFun (IN (_, lvar1, _, _, _), IN (_, lvar2, _, _, _)) =
            LambdaVar.same (lvar1, lvar2)
        | sameFun (OUT, OUT) = true
        | sameFun _ = false
      fun sameKey (FUN f1, FUN f2) =
            sameFun (f1, f2)
        | sameKey (RECORD a, RECORD b) =
            ListPair.allEq sameAddr (a, b)
        | sameKey (REF a, REF b) =
            sameAddr (a, b)
        | sameKey (DATA, DATA) = true (* TODO: CHECK *)
        | sameKey (UNKNOWN _, UNKNOWN _) = true
        | sameKey _ = false

      fun hashVal v =
        let
          val dataTag    = 0w0
          val funTag     = 0w1
          val recordTag  = 0w2
          val refTag     = 0w3
          val topTag     = 0w4
          val unknownTag = 0w5
          fun addTag (hash, tag) = Word.orb (Word.<< (hash, 0w3), tag)
        in
          case v
            of DATA => dataTag
             | UNKNOWN _ => unknownTag
             | FUN (IN (_, lvar, _, _, _)) =>
                 addTag (Word.fromInt (LambdaVar.toId lvar), funTag)
             | FUN OUT => topTag
             | RECORD addrs =>
                 addTag (foldl (fn (v, h) => hashCombine (h, hashAddr v))
                               0w0
                               addrs,
                         recordTag)
             | REF addr => addTag (Word.fromInt (LambdaVar.toId addr), refTag)
        end
    end)

    type t = Set.set
    val mk = Set.mkSingleton
    val from = Set.mkFromList
    val copy = Set.copy
    val app = Set.app
    val toList = Set.toList

    fun add (set, v) =
      if Set.member (set, v) then
        false
      else
        (Set.add (set, v); true)

    fun merge (set1, set2) =
      Set.fold (fn (v, changed) => add (set1, v) orelse changed) false set2

    fun collect sieve fold set =
      fold (fn (v, result) => case sieve v
                                of SOME data => data :: result
                                 | NONE => result) [] set

    val say = print
    val sayLvar = say o LambdaVar.lvarName

    fun dumpC (FUN (IN (_, name, _, _, _))) =
          say (LambdaVar.lvarName name ^ "[F]")
      | dumpC (FUN OUT) =
          say ("Foreign")
      | dumpC (RECORD addrs) =
          (say "{";
           say (String.concatWithMap ", " LambdaVar.lvarName addrs);
           say "} [R]")
      | dumpC (REF addrs) =
          say (LambdaVar.lvarName addrs ^ "[REF]")
      | dumpC DATA =
          say "[D]"
      | dumpC (UNKNOWN cty) =
          say ("U" ^ CPSUtil.ctyToString cty)

    fun dump set = (say "["; Set.app (fn c => (dumpC c; say ",")) set; say "]")

    val objects =
      let fun collect (FUN (IN f), SOME (CallGraph.Function fs)) =
                SOME (CallGraph.Function (CallGraph.In f :: fs))
            | collect (FUN (IN f), NONE) =
                SOME (CallGraph.Function [CallGraph.In f])
            | collect (FUN OUT, SOME (CallGraph.Function fs)) =
                if List.exists (fn CallGraph.Out => true | _ => false) fs then
                  SOME (CallGraph.Function fs)
                else
                  SOME (CallGraph.Function (CallGraph.Out :: fs))
            | collect (FUN OUT, NONE) =
                SOME (CallGraph.Function [CallGraph.Out])

            | collect (FUN (IN f), SOME CallGraph.Value) =
                (* FIXME GROSS HACK: Some values in CPS may be bound to both an
                 * integer and a function pointer. For example, a value of
                 * datatype t = A of int -> int | B will be represented by one
                 * ML value -- (A f) is a pointer whereas B is an integer.
                 * Call-sites discriminate the cases by testing if the value
                 * is boxed. *)
                SOME (CallGraph.Function [CallGraph.In f, CallGraph.Out])
            | collect (FUN OUT, SOME CallGraph.Value) =
                SOME (CallGraph.Function [CallGraph.Out])

            | collect (FUN _, SOME _) =
                raise Fail "conflicting 1"
            | collect (RECORD data,
                       (NONE | SOME CallGraph.Value)) =
                SOME CallGraph.Value
            | collect (RECORD data, SOME _) =
                raise Fail "conflicting 2"
            | collect (REF _,
                       (NONE | SOME CallGraph.Value)) =
                SOME CallGraph.Value
            | collect (REF _, SOME _) =
                raise Fail "conflicting 3"
            | collect (DATA, (NONE | SOME CallGraph.Value)) =
                SOME CallGraph.Value
            | collect (DATA, SOME (CallGraph.Function fs)) =
                if List.exists (fn CallGraph.Out => true | _ => false) fs then
                  SOME (CallGraph.Function fs)
                else
                  SOME (CallGraph.Function (CallGraph.Out :: fs))
            | collect (DATA, _) =
                raise Fail "conflicting 4"
            | collect (UNKNOWN cty, (NONE | SOME CallGraph.Value)) =
                SOME CallGraph.Value
            | collect (UNKNOWN _, SOME _) =
                raise Fail "conflicting 5"
      in  fn v => (Option.valOf o (Set.fold collect NONE)) v
          handle Fail conflict => (print (conflict ^ ": "); dump v; print "\n"; raise Fail
          conflict)
      end

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
    (* val setTop: t -> CPS.lvar -> bool *)
    val getHdlr: t -> Value.t
    val addHdlr: t -> Value.t -> bool
    val merge: t -> CPS.lvar * Value.t -> bool
    val lookup: t -> CPS.lvar -> Value.t
    val find: t -> CPS.lvar -> Value.t option
    val dump: t -> unit
  end = struct
    structure LVarTbl = LambdaVar.Tbl

    type t = {epoch: int ref, table: Value.t LVarTbl.hash_table, hdlr: Value.t}

    exception StoreLookUp
    fun new () =
      { epoch=ref 0
      , table=LVarTbl.mkTable (32, StoreLookUp)
      , hdlr=Value.mk (Value.FUN Value.OUT)
      }

    fun epoch ({epoch, ...}: t) = !epoch

    fun updateEpoch epoch true  = (epoch := !epoch + 1; true)
      | updateEpoch epoch false = false

    fun update {epoch, table, hdlr=_} (lvar, v) =
      case LVarTbl.find table lvar
        of SOME set => updateEpoch epoch (Value.add (set, v))
         | NONE => (LVarTbl.insert table (lvar, Value.mk v);
                    updateEpoch epoch true)

    (* fun setTop {epoch, table, hdlr=_} lvar = *)
    (*   case LVarTbl.find table lvar *)
    (*     of SOME set => updateEpoch epoch (Value.setTop set) *)
    (*      | NONE => (LVarTbl.insert table (lvar, Value.mk Value.T); *)
    (*                 updateEpoch epoch true) *)

    fun merge {epoch, table, hdlr=_} (lvar, value) =
      case LVarTbl.find table lvar
        of SOME orig => updateEpoch epoch (Value.merge (orig, value))
         | NONE => (LVarTbl.insert table (lvar, Value.copy value);
                    updateEpoch epoch true)

    (* fun merge {epoch, table, hdlr=_} (lvar, value) = *)
    (*   case LVarTbl.find table lvar *)
    (*     of SOME orig => *)
    (*          let val changed = Value.merge (orig, value) *)
    (*          in  (if !epoch > 10000 andalso changed then *)
    (*                (print ("\n" ^ LambdaVar.lvarName lvar ^ " ---> "); *)
    (*                Value.dump orig; *)
    (*                print "\n") *)
    (*              else *)
    (*                ()); *)
    (*              updateEpoch epoch changed *)
    (*          end *)
    (*      | NONE => (LVarTbl.insert table (lvar, Value.copy value); *)
    (*                 updateEpoch epoch true) *)

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

    (* fun dump _ = () *)

    fun lookup (s as {table, ...}: t) lvar = LVarTbl.lookup table lvar
      handle StoreLookUp => (say "LOOKUP FAIL: ";
                             say (LambdaVar.lvarName lvar);
                             say "\n";
                             dump s;
                             raise StoreLookUp)

    fun find (s as {table, ...}: t) lvar = LVarTbl.find table lvar
  end

  exception Unimp
  exception Impossible of string
  structure Context :> sig
    type t

    structure FunctionSet : ORD_SET where type Key.ord_key = LCPS.function

    val new: unit -> t
    val guard: (t -> LCPS.cexp -> unit) -> t -> LCPS.cexp -> unit
    val lookup: t -> LCPS.lvar -> Value.t
    val find: t -> LCPS.lvar -> Value.t option
    val add: t -> (LCPS.lvar * Value.concrete) -> bool
    val merge: t -> (LCPS.lvar * Value.t) -> bool
    val dump: t -> unit
    val escape: t -> LCPS.lvar -> unit
    val escapeSet: t -> FunctionSet.set
    val epoch: t -> int
    val getHdlr: t -> Value.t
    val addHdlr: t -> Value.t -> unit
  end = struct

    structure FunctionSet = RedBlackSetFn(struct
      type ord_key = LCPS.function
      fun compare (f1: ord_key, f2: ord_key) = LambdaVar.compare (#2 f1, #2 f2)
    end)

    structure LambdaVarSet = HashSetFn(struct
      type hash_key = LambdaVar.lvar
      val sameKey = LambdaVar.same
      val hashVal = Word.fromInt o LambdaVar.toId
    end)

    type t = { epochTable: int LCPS.Tbl.hash_table
             , store: Store.t
             , escapeSet: FunctionSet.set ref
             , escapingAddr: LambdaVarSet.set
             }

    exception EpochLookUp
    fun new () =
      { epochTable = LCPS.Tbl.mkTable (1024, EpochLookUp)
      , store = Store.new ()
      , escapeSet = ref FunctionSet.empty
      , escapingAddr = LambdaVarSet.mkEmpty 2048
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
           (* print ("\r" ^ Int.toString currEpoch); *)
           f ctx cexp)
      end

    fun dump {epochTable, store, escapeSet, escapingAddr} =
      (Store.dump store;
       print "\nEscaping: {";
       FunctionSet.app (fn x => print (LambdaVar.lvarName (#2 x) ^ ","))
                        (!escapeSet);
       print "}\n")

    (* fun dump _ = () *)

    val lookup = Store.lookup o (fn (ctx: t) => #store ctx)
    val find = Store.find o (fn (ctx: t) => #store ctx)

    fun scanValue (Value.FUN (Value.IN f), (todo, result)) =
          (todo, FunctionSet.add (result, f))
      | scanValue (Value.FUN Value.OUT, acc) = acc
      | scanValue (Value.RECORD addrs, (todo, result)) =
          (addrs @ todo, result)
      | scanValue (Value.REF addr, (todo, result)) =
          (addr :: todo, result)
      | scanValue (Value.DATA, acc) = acc
      | scanValue (Value.UNKNOWN _, acc) = acc
    and scanAddr ctx seen result [] = result
      | scanAddr ctx seen result (addr::todo) =
          if LambdaVar.Set.member (seen, addr) then
            scanAddr ctx seen result todo
          else
            let
              val seen' = LambdaVar.Set.add (seen, addr)
              val (todo', result') =
                foldl scanValue (todo, result) (Value.toList (lookup ctx addr))
            in
              scanAddr ctx seen' result' todo'
            end

    fun addEscapingFun (ctx: t) name =
      let val escapeSet = #escapeSet ctx
      in  escapeSet := scanAddr ctx LambdaVar.Set.empty (!escapeSet) [name]
      end

    fun escape (ctx: t) name =
      let val escapingAddr = #escapingAddr ctx
      in  if LambdaVarSet.member (escapingAddr, name) then
            (* if we knew that this address is escaping already, nothing needs
             * to be done here since any value added to this address is marked
             * as escaping *)
             ()
          else
            (LambdaVarSet.add (escapingAddr, name);
             addEscapingFun ctx name)
      end

    fun add (ctx: t) (addr, c) =
      (if LambdaVarSet.member (#escapingAddr ctx, addr) then
        let val (addrs, escapeSet) = scanValue (c, ([], !(#escapeSet ctx)))
            val () = app (escape ctx) addrs
        in  (#escapeSet ctx) := escapeSet
        end
       else ();
       Store.update (#store ctx) (addr, c))

    fun merge (ctx: t) (addr, v) =
      (if LambdaVarSet.member (#escapingAddr ctx, addr) then
        let val (addrs, escapeSet) =
              foldl scanValue ([], !(#escapeSet ctx)) (Value.toList v)
            val () = app (escape ctx) addrs
        in  (#escapeSet ctx) := escapeSet
        end
       else ();
       Store.merge (#store ctx) (addr, v))

    fun epoch ({store, ...}: t) = Store.epoch store
    fun escapeSet ({escapeSet, ...}: t) = !escapeSet
  end

  fun evalValue ctx (CPS.VAR v) =
        Context.lookup ctx v
    | evalValue ctx (CPS.LABEL _) =
        raise (Impossible "Label value before closure conversion")
    | evalValue _ CPS.VOID =
        (* Gross hack *)
        Value.mk Value.DATA
    | evalValue _ (CPS.NUM _ | CPS.REAL _ | CPS.STRING _) =
        Value.mk Value.DATA

  fun unknown (CPS.FUNt | CPS.CNTt) = Value.FUN Value.OUT
    | unknown (CPS.NUMt _ | CPS.FLTt _) = Value.DATA
    | unknown cty = Value.UNKNOWN cty

  fun select ctx (values, off, cty) =
    let fun collect (Value.RECORD addrs, acc) =
              ((Context.lookup ctx (List.nth (addrs, off)) :: acc)
               handle Subscript => acc)
          | collect (Value.UNKNOWN (CPS.PTRt _), acc) =
              (Value.mk (unknown cty) :: acc)
          | collect (_, acc) = acc
    in  foldr collect [] values
    end

  fun access ctx =
    let fun go (concretes, CPS.OFFp 0) = concretes
          | go (concretes, CPS.OFFp i) =
              let fun offset addrs = SOME (Value.RECORD (List.drop (addrs, i)))
                                     handle Subscript => NONE
                  fun collect (Value.RECORD addrs, acc) =
                        (case offset addrs
                           of SOME c => c :: acc
                            | NONE   => acc)
                    | collect (Value.UNKNOWN (CPS.PTRt _), acc) =
                        (Value.UNKNOWN (CPS.PTRt CPS.VPT) :: acc)
                    | collect (_, acc) = acc
              in  foldr collect [] concretes
              end
          | go (concretes, CPS.SELp (i, p)) =
              let fun get addrs =
                    (let val addr = List.nth (addrs, i)
                         val values = Value.toList (Context.lookup ctx addr)
                     in  go (values, p)
                     end)
                    handle Subscript => []
                  fun collect (Value.RECORD addrs, acc) =
                        get addrs @ acc
                    | collect (Value.UNKNOWN (CPS.PTRt _), acc) =
                        (Value.UNKNOWN (CPS.PTRt CPS.VPT) :: acc)
                    | collect (_, acc) = acc
              in  foldr collect [] concretes
              end
    in  go
    end

  fun dump ctx cexp =
    (print "Current expression:\n";
     PPCps.prcps (LCPS.unlabel cexp);
     print "\nCurrent state:\n";
     Context.dump ctx;
     print "=================\n\n\n")
  fun dump ctx cexp =
    if Context.epoch ctx > 10000 then
      (print ("\ncurrent epoch:          " ^ Int.toString (Context.epoch ctx));
       Context.dump ctx;
       print "=================\n\n\n")
    else
      ()
  fun dump ctx cexp = 
    print ("\rcurrent epoch:          " ^ Int.toString (Context.epoch ctx))

  fun loopExp ctx cexp = (dump ctx cexp; Context.guard loopExpCase ctx cexp)
  and loopExpCase ctx (LCPS.APP (_, f, args)) =
        apply ctx (evalValue ctx f, args)
    | loopExpCase ctx (LCPS.RECORD (_, _, values, x, body)) =
        let
          fun alloc (dest, src, path) =
            let val concretes = access ctx
                                       (Value.toList (evalValue ctx src), path)
                val value = Value.from concretes
            in  Context.merge ctx (dest, value); dest
            end
          val record = Value.RECORD (map alloc values)
        in
          Context.add ctx (x, record);
          loopExp ctx body
        end
    | loopExpCase ctx (LCPS.SELECT (_, i, value, dest, ty, body)) =
        let val values = select ctx (Value.toList (evalValue ctx value), i, ty)
        in  case values
              of [] => () (* no record value is accessible here; type error *)
               | _ =>
                   (app (fn v => ignore (Context.merge ctx (dest, v))) values;
                    loopExp ctx body)
        end
    | loopExpCase ctx (LCPS.OFFSET (_, i, value, dest, body)) =
        raise Fail "no OFFSET"
        (* let val v = *)
        (*       let val records = Value.records (evalValue ctx value) *)
        (*           fun truncate addrs = *)
        (*             SOME (Value.RECORD (List.drop (addrs, i))) *)
        (*             handle Subscript => NONE *)
        (*           val records' = List.mapPartial truncate records *)
        (*       in  Value.from records' *)
        (*       end *)
        (* in  Context.merge ctx (dest, v); *)
        (*     loopExp ctx body *)
        (* end *)
    | loopExpCase ctx (LCPS.FIX (_, bindings, body)) =
        let fun bind (f as (_, name, _, _, _)) =
              ignore (Context.add ctx (name, Value.FUN (Value.IN f)))
        in  app bind bindings;
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
    | loopExpCase ctx (LCPS.SETTER (_, (CPS.P.UNBOXEDASSIGN | CPS.P.ASSIGN),
                                       [dest, src], body)) =
        let val srcVal = evalValue ctx src
            fun assign (Value.REF addr) =
                  ignore (Context.merge ctx (addr, srcVal))
              | assign (Value.UNKNOWN (CPS.PTRt _)) =
                  (* when dest has unknown value, src escapes *)
                  (case src
                     of CPS.VAR var => Context.escape ctx var
                      | _ => ())
              | assign _ = ()
        in  Value.app assign (evalValue ctx dest); loopExp ctx body
        end
    | loopExpCase ctx (LCPS.SETTER (_, (CPS.P.UNBOXEDASSIGN | CPS.P.ASSIGN),
                                       _, _)) =
        raise Impossible "ASSIGN takes wrong arguments"
    | loopExpCase ctx (LCPS.SETTER (_, _, _, body)) =
        loopExp ctx body
    | loopExpCase ctx (LCPS.LOOKER (_, CPS.P.GETHDLR, [], dest, _, body)) =
        (Context.merge ctx (dest, Context.getHdlr ctx);
         loopExp ctx body)
    | loopExpCase ctx (LCPS.LOOKER (_, CPS.P.GETHDLR, _, dest, _, body)) =
        raise Impossible "GETHDLR does not take arguments"
    | loopExpCase ctx (LCPS.LOOKER (_, CPS.P.DEREF, [cell], dest, ty, body)) =
        let fun deref (Value.REF addr) =
                  ignore (Context.merge ctx (dest, Context.lookup ctx addr))
              | deref (Value.UNKNOWN (CPS.PTRt _)) =
                  ignore (Context.add ctx (dest, unknown ty))
              | deref _ = ()
        in  Value.app deref (evalValue ctx cell);
            loopExp ctx body
        end
    | loopExpCase ctx (LCPS.LOOKER (_, CPS.P.DEREF, _, _, _, _)) =
        raise Impossible "DEREF with wrong number of arguments"
    | loopExpCase ctx (LCPS.LOOKER (_, _, _, dest, ty, body)) =
        (Context.add ctx (dest, unknown ty); loopExp ctx body)
    | loopExpCase ctx (LCPS.ARITH (_, _, _, dest, ty, body)) =
        (* FIXME: stop using VOID *)
        (apply ctx (Context.getHdlr ctx, [CPS.VOID, CPS.VOID]);
         Context.add ctx (dest, Value.DATA);
         loopExp ctx body)
    | loopExpCase ctx (LCPS.PURE (label, CPS.P.MAKEREF, [v], dest, ty, body)) =
        (Context.add ctx (dest, Value.REF label);
         case v
           of CPS.VAR w => Context.merge ctx (label, Context.lookup ctx w)
            | CPS.LABEL _ => raise Impossible "label"
            | (CPS.NUM _ | CPS.REAL _ | CPS.STRING _) =>
                Context.add ctx (label, Value.DATA)
            | CPS.VOID => raise Impossible "what is this?";
         loopExp ctx body)
    | loopExpCase ctx (LCPS.PURE (_, _, _, dest, ty, body)) =
        (Context.add ctx (dest, unknown ty); loopExp ctx body)
    | loopExpCase ctx (LCPS.RCC _) =
        raise Unimp
  and apply ctx (f: Value.t, args: LCPS.value list) =
        let
          val argVals = map (evalValue ctx) args
          fun call (Value.FUN (Value.IN (_, name, formals, types, body))) =
                ((app (ignore o Context.merge ctx)
                     (ListPair.zipEq (formals, argVals));
                  loopExp ctx body)
                 handle ListPair.UnequalLengths => ())
                (* if the function is applied with incorrect number
                 * of arguments, this path is aborted *)
             | call (Value.FUN Value.OUT) =
                 app (fn (CPS.VAR v) => Context.escape ctx v | _ => ()) args
             (* | call Value.UNCAUGHTEXN = *)
             (*     app (fn (CPS.VAR v) => Context.escape ctx v | _ => ()) args *)
             | call (Value.RECORD _ | Value.REF _ | Value.DATA |
                     Value.UNKNOWN _) =
                 raise Fail "does this happen?"
                (* if applying a non-function, nothing to be done *)
        in
          Value.app call f
        end

  (* fun loopEscape ctx q visited = *)
  (*   let *)
  (*     fun doFunction (fun_kind, name, formals, tys, body) = *)
  (*       let *)
  (*         val beforeSet = Context.escapeSet ctx *)
  (*         fun mkUnknown (arg, cty) = ignore (Context.add ctx (arg, unknown cty)) *)
  (*       in *)
  (*         ListPair.appEq mkUnknown (formals, tys); *)
  (*         loopExp ctx body; *)
  (*         Context.FunctionSet.app (fn f => Queue.enqueue (q, f)) *)
  (*           (Context.FunctionSet.difference (Context.escapeSet ctx, beforeSet)); *)
  (*         () *)
  (*       end *)
  (*   in *)
  (*     case Queue.next q *)
  (*       of SOME (function as (_, name, _, _, _)) => *)
  (*            if LambdaVar.Set.member (visited, name) then *)
  (*              loopEscape ctx q visited *)
  (*            else *)
  (*              (doFunction function; *)
  (*               loopEscape ctx q (LambdaVar.Set.add (visited, name)); *)
  (*               ()) *)
  (*        | NONE => () *)
  (*   end *)

  fun loopEscape ctx q visited =
    let
      fun doFunction (funkind, name, formals, tys, body) =
        let fun addArg (arg, cty) = ignore (Context.add ctx (arg, unknown cty))
        in  ListPair.appEq addArg (formals, tys);
            loopExp ctx body
        end
      fun enqueueChanged () =
        let val currEpoch = Context.epoch ctx
            fun addFun function =
              case LCPS.FunTbl.find visited function
                of SOME epoch => 
                     if currEpoch > epoch then
                       Queue.enqueue (q, function)
                     else
                       ()
                 | NONE => Queue.enqueue (q, function)
            val escaped = Context.escapeSet ctx
        in  Context.FunctionSet.app addFun escaped
        end
      fun needToVisit f =
        case LCPS.FunTbl.find visited f
          of SOME epoch => Context.epoch ctx > epoch
           | NONE => true
      (* val () = (print "Queue: "; Queue.app *) 
      (*   (fn f => print (LambdaVar.lvarName (#2 f) ^ ", ")) q; *)
      (*   print "\n") *)
      val () = print ("\rQueue length: " ^ Int.toString (Queue.length q))
    in
      case Queue.next q
        of SOME function =>
             if needToVisit function then
               (LCPS.FunTbl.insert visited (function, Context.epoch ctx);
                doFunction function;
                enqueueChanged ();
                loopEscape ctx q visited)
             else
               loopEscape ctx q visited
         | NONE => ()
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

  fun analyze function =
    let
      val ctx = Context.new ()
      val queue = Queue.mkQueue ()
      val visited = LCPS.FunTbl.mkTable (32, Fail "visited table")
      val () = Queue.enqueue (queue, function)
      val () = ignore
        (Context.add ctx (#2 function, Value.FUN (Value.IN function)))
    in
      timeit "\r\n0cfa: " (fn () => loopEscape ctx queue visited);
      Context.dump ctx;
      CallGraph.build {cps=function,
                       lookup=Option.map Value.objects o Context.find ctx,
                       escapingLambdas=Vector.fromList
                       (function ::
                        Context.FunctionSet.toList (Context.escapeSet ctx))}
    end
end
