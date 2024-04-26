signature CALL_GRAPH = sig
  type t

  datatype function
    = In of LabelledCPS.function
    | Out
  datatype object
    = Value
    | FirstOrder of LabelledCPS.function
    | Function of function list
    | NoBinding

  datatype info
    = Escape
    | Unreachable
    | Known of { callers: LabelledCPS.function list }
    | Family of family_info list
  withtype family_info = { caller: LabelledCPS.function,
                           colleagues: LabelledCPS.function vector option }

  datatype component = Single of LabelledCPS.function
                     | Group of LabelledCPS.function list

  val build : {
    cps: LabelledCPS.function,
    lookup : CPS.lvar -> object option,
    escapingLambdas: LabelledCPS.function vector
  } -> t

  val bogus : unit -> t

  val scc : t -> component list
  val info   : t -> LabelledCPS.function -> info
  val whatis : t -> LabelledCPS.lvar -> object

  val predecessors : t -> LabelledCPS.function -> LabelledCPS.function list
  val successors : t -> LabelledCPS.function -> LabelledCPS.function list

  val allFunctions : t -> LabelledCPS.function vector
  val knownFunctions : t -> LabelledCPS.function vector
  val escapingFunctions : t -> LabelledCPS.function vector

  val callGraphDot : t -> DotLanguage.t
  (* val callWebDot : t -> DotLanguage.t *)

  val dumpStats : t -> unit
end

structure CallGraph :> CALL_GRAPH = struct
  structure LV = LambdaVar
  structure LCPS = LabelledCPS

  datatype function
    = In of LabelledCPS.function
    | Out
  datatype object
    = Value
    | FirstOrder of LabelledCPS.function
    | Function of function list
    | NoBinding

  datatype info
    = Escape
    | Unreachable
    | Known of { callers: LabelledCPS.function list }
    | Family of family_info list
  withtype family_info = { caller: LabelledCPS.function,
                           colleagues: LabelledCPS.function vector option }

  datatype component = Single of LabelledCPS.function
                     | Group of LabelledCPS.function list

  datatype t = T of {
    funTbl: info LCPS.FunTbl.hash_table,
    varTbl: object LV.Tbl.hash_table,
    allFunctions: LCPS.function vector,
    knownFunctions: LCPS.function vector,
    escaping: LCPS.function vector
  }

  val funstr = LV.lvarName o LCPS.nameOfF

  fun objToString Value = "(Value)"
    | objToString (FirstOrder f) = "(FO)" ^ funstr f
    | objToString (Function fs) =
        let fun fToS Out = "Out" | fToS (In f) = funstr f
        in  concat ["(F) [", String.concatWithMap ", " fToS fs, "]"]
        end
    | objToString NoBinding = "(NoBind)"

  fun infoToString Escape = "(Escape)"
    | infoToString Unreachable = "(Unreachable)"
    | infoToString (Known {callers}) =
        concat ["(Known) [", String.concatWithMap ", " funstr callers, "]"]
    | infoToString (Family family) =
       let fun pf {caller, colleagues=NONE} =
                 concat [funstr caller, "-->{}"]
             | pf {caller, colleagues=SOME fs} =
                 concat [funstr caller, "-->{",
                         String.concatWithMap "," funstr (Vector.toList fs),
                         "}"]
       in  concat ["(Family) [", String.concatWithMap ", " pf family, "]"]
       end

  fun sameFun f1 f2 = LV.same (LCPS.nameOfF f1, LCPS.nameOfF f2)

  exception CallGraph

  fun bogus () = 
      T { funTbl=LCPS.FunTbl.mkTable (0, CallGraph),
          varTbl=LV.Tbl.mkTable (0, CallGraph),
          allFunctions=Vector.fromList [],
          knownFunctions=Vector.fromList [],
          escaping= #[] }

  fun build {cps, lookup, escapingLambdas} =
    let
      val funTbl = LCPS.FunTbl.mkTable (64, CallGraph)
      val varTbl = LV.Tbl.mkTable (1024, CallGraph)
      val allFunctions = ref ([] : LCPS.function list)
      val knownFunctions = ref ([] : LCPS.function list)

      fun merge _ (Escape, _) = Escape
        | merge _ (_, Escape) = Escape
        | merge _ (info, Unreachable) = info
        | merge _ (Unreachable, info) = info
        | merge _ (Known {callers=callers1}, Known {callers=callers2}) =
            Known {callers=callers1 @ callers2}
        | merge self ((Known {callers}, Family family) |
                      (Family family, Known {callers})) =
            let val family' = map (fn f => {caller=f, colleagues=SOME #[self]})
                                  callers
            in  Family (family' @ family)
            end
        | merge _ (Family family, Family family') =
            Family (family' @ family)

      fun updateInfo (f, info) =
        case LCPS.FunTbl.find funTbl f
          of NONE       => LCPS.FunTbl.insert funTbl (f, info)
           | SOME info' => LCPS.FunTbl.insert funTbl (f, merge f (info, info'))

      fun updateCall (callerF, var) =
        case LV.Tbl.lookup varTbl var
          of Value => raise Fail "not a function"
           | NoBinding => ()
           | FirstOrder f => updateInfo (f, Known { callers=[callerF] })
           | Function [] => raise Fail "object is not bound"
           | Function [In f] => updateInfo (f, Known { callers=[callerF] })
           | Function fs  =>
               let
                 val coll = foldr (fn (In f, SOME fs) => SOME (f :: fs)
                                    | (In f, NONE) => NONE
                                    | (OUT, _) => NONE)
                                  (SOME []) fs
                 val family = { caller=callerF,
                                colleagues=Option.map Vector.fromList coll }
                 fun update (In f) = updateInfo (f, Family [family])
                   | update OUT = ()
               in
                 app update fs
               end

      fun cacheObj name =
        case lookup name
          of SOME obj => LV.Tbl.insert varTbl (name, obj)
           | NONE     => LV.Tbl.insert varTbl (name, NoBinding)

      fun initF function =
        (case lookup (#2 function)
           of SOME _ => ()
            | NONE   => print ("not bound " ^ LV.lvarName (#2 function) ^ "\n");
        if Vector.exists (sameFun function) escapingLambdas then
          updateInfo (function, Escape)
        else
          updateInfo (function, Unreachable))

      fun bindF (function as (_, name, _, _, _)) =
        LV.Tbl.insert varTbl (name, FirstOrder function)

      fun walkF (function as (_, name, args, _, body)) =
        let
          val () = allFunctions := function :: (!allFunctions)
          val () = if Vector.exists (sameFun function) escapingLambdas then
                     ()
                   else
                     knownFunctions := function :: (!knownFunctions)
          val () = app cacheObj args
          fun exp (LCPS.APP (_, CPS.VAR f, _)) = updateCall (function, f)
            | exp (LCPS.APP _) = raise Fail "app not var"
            | exp (LCPS.FIX (_, bindings, body)) =
                (app initF bindings;
                 app bindF bindings;
                 app walkF bindings;
                 exp body)
            | exp (LCPS.SWITCH (_, _, _, es)) = app exp es
            | exp (LCPS.BRANCH (_, _, _, _, te, fe)) = (exp te; exp fe)
            | exp (LCPS.RECORD (_, _, _, name, e) |
                   LCPS.SELECT (_, _, _, name, _, e) |
                   LCPS.OFFSET (_, _, _, name, e) |
                   LCPS.LOOKER (_, _, _, name, _, e) |
                   LCPS.ARITH  (_, _, _, name, _, e) |
                   LCPS.PURE   (_, _, _, name, _, e)) =
                (cacheObj name; exp e)
            | exp (LCPS.SETTER (_, _, _, e)) = exp e
            | exp (LCPS.RCC    (_, _, _, _, _, returns, e)) =
                (app (cacheObj o #1) returns; exp e)
        in
          exp body
        end
      val () = Vector.app (fn f => LCPS.FunTbl.insert funTbl (f, Escape))
                          escapingLambdas
    in
      walkF cps;
      T { funTbl=funTbl,
          varTbl=varTbl,
          allFunctions=Vector.fromList (!allFunctions),
          knownFunctions=Vector.fromList (!knownFunctions),
          escaping=escapingLambdas }
    end

  fun bug msg = (print (msg ^ "\n"); raise CallGraph)

  fun whatis (T {varTbl, ...}) v =
    case LV.Tbl.find varTbl v
      of SOME obj => obj
       | NONE => bug ("whatis " ^ LV.lvarName v ^ " failed")

  fun info (T {funTbl, varTbl, ...}) f =
    case LCPS.FunTbl.find funTbl f
      of SOME data => data
       | NONE => bug ("info " ^ LV.lvarName (#2 f) ^ " failed")

  fun knownFs fs =
    foldr (fn (In f, acc) => f :: acc | (Out, acc) => acc) [] fs

  fun predecessors t function =
    case info t function
      of Escape => []
       | Unreachable => []
       | Known {callers} => callers
       | Family families => map #caller families

  fun successors t (function as (_, _, _, _, body)) =
    let
      fun fold (LCPS.APP (_, CPS.VAR f, args), acc) =
            (case whatis t f
               of Value => raise Fail "not a function"
                | FirstOrder f => f :: acc
                | Function fs =>
                    let fun escapes (CPS.VAR f, acc) =
                              (case whatis t f
                                 of Function fs => knownFs fs @ acc
                                  | FirstOrder f => f :: acc
                                  | Value => acc
                                  | NoBinding => acc) (* raise Fail "??" *)
                          | escapes (_, acc) = acc

                        fun collect (In f, acc) = f :: acc
                          | collect (Out, acc) = foldl escapes acc args
                    in  foldl collect acc fs
                    end
                | _ => acc)
        | fold (LCPS.APP _, acc) = raise Fail "call not a var"
        | fold (LCPS.SWITCH  (_, _, _, es), acc) = foldr fold acc es
        | fold (LCPS.BRANCH  (_, _, _, _, te, fe), acc) =
            fold (fe, fold (te, acc))
        | fold ((LCPS.FIX    (_, _, e) |
                 LCPS.RECORD (_, _, _, _, e) |
                 LCPS.SELECT (_, _, _, _, _, e) |
                 LCPS.OFFSET (_, _, _, _, e) |
                 LCPS.SETTER (_, _, _, e) |
                 LCPS.LOOKER (_, _, _, _, _, e) |
                 LCPS.ARITH  (_, _, _, _, _, e) |
                 LCPS.PURE   (_, _, _, _, _, e) |
                 LCPS.RCC    (_, _, _, _, _, _, e)), acc) = fold (e, acc)
    in
      fold (body, [])
    end

  fun allFunctions (T {allFunctions, ...}) = allFunctions
  fun knownFunctions (T {knownFunctions, ...}) = knownFunctions
  fun escapingFunctions (T {escaping, ...}) = escaping

  structure SCCSolver = GraphSCCFn(struct
    type ord_key = LCPS.function
    fun compare (f1: ord_key, f2: ord_key) = LambdaVar.compare (#2 f1, #2 f2)
  end)

  fun toGraph (t as T {escaping, ...}) =
    { roots=Vector.toList escaping, follow=successors t }

  fun scc cg =
    let
      fun convert (SCCSolver.SIMPLE f) = Single f
        | convert (SCCSolver.RECURSIVE fs) = Group fs
    in
      map convert (SCCSolver.topOrder' (toGraph cg))
    end

  fun callGraphDot (cg as T {escaping, ...}) =
    let fun escapes (f: LCPS.function) =
          Vector.exists (fn f' => LV.same (#2 f, #2 f')) escaping
        fun convert (f: LCPS.function) =
          (LV.lvarName (#2 f), if escapes f then [("color", "red")] else [])
    in  DotLanguage.fromGraph convert (toGraph cg)
    end

  fun dumpStats (t as T {allFunctions, ...}) =
    let
      val nFirstOrder = ref 0
      val distr = IntHashTable.mkTable (32, Fail "distr")
      fun incr n =
        (case IntHashTable.find distr n
           of NONE   => IntHashTable.insert distr (n, 1)
            | SOME c => IntHashTable.insert distr (n, c + 1))
      val incr = fn n => (if n >= 10 then incr 10 else incr n)
      val polluted = ref 0
      val hasOut = List.exists (fn Out => true | _ => false)
      val total = ref 0
      fun fold (LCPS.APP (_, CPS.VAR f, args), acc) =
            (total := !total + 1;
             case whatis t f
               of Value => ()
                | FirstOrder f => (nFirstOrder := !nFirstOrder + 1)
                | Function fs =>
                    ((if hasOut fs then (polluted := !polluted + 1) else ());
                     incr (List.length (knownFs fs)))
                | NoBinding => ())
        | fold (LCPS.APP _, acc) = raise Fail "call not a var"
        | fold (LCPS.SWITCH  (_, _, _, es), acc) = foldr fold acc es
        | fold (LCPS.BRANCH  (_, _, _, _, te, fe), acc) =
            fold (fe, fold (te, acc))
        | fold ((LCPS.FIX    (_, _, e) |
                 LCPS.RECORD (_, _, _, _, e) |
                 LCPS.SELECT (_, _, _, _, _, e) |
                 LCPS.OFFSET (_, _, _, _, e) |
                 LCPS.SETTER (_, _, _, e) |
                 LCPS.LOOKER (_, _, _, _, _, e) |
                 LCPS.ARITH  (_, _, _, _, _, e) |
                 LCPS.PURE   (_, _, _, _, _, e) |
                 LCPS.RCC    (_, _, _, _, _, _, e)), acc) = fold (e, acc)
      val () = Vector.app (fn (f as (_, _, _, _, body)) => fold (body, ()))
                          allFunctions
    in
      print (">> total: " ^ Int.toString (!total) ^ "\n");
      print (">> nFirstOrder: " ^ Int.toString (!nFirstOrder) ^ "\n");
      print (">> polluted: " ^ Int.toString (!polluted) ^ "\n");
      print (">> distr:\n>>\t" ^ String.concatWithMap "\n>>\t"
      (fn (n, c) => Int.toString n ^ " --> " ^ Int.toString c)
      (IntHashTable.listItemsi distr) ^ "\n");
      ()
    end

end
