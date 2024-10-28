structure Web :> sig
  type id
  type t
  datatype kind = User | Cont

  type info = {
    defs: LabelledCPS.function vector,
    uses: LabelledCPS.lvar vector,
    polluted: bool,
    kind: kind
  }

  val calculate : FlowCFA.result * SyntacticInfo.t -> t

  val webOfVar : t * LabelledCPS.lvar -> id option
  val webOfFun : t * LabelledCPS.function -> id

  val defs : t * id -> LabelledCPS.function vector
  val uses : t * id -> LabelledCPS.lvar vector
  val content : t * id -> info
  val polluted : t * id -> bool
  val kind : t * id -> kind
  val kindOfCty : CPS.cty -> kind

  val fold : (id * info * 'a -> 'a) -> 'a -> t -> 'a

  val idToString : id -> string
  val toString : info -> string

  val dump : t -> unit

  structure Map : ORD_MAP where type Key.ord_key = id
  structure Set : ORD_SET where type Key.ord_key = id
  structure Tbl : MONO_HASH_TABLE where type Key.hash_key = id
end = struct
  structure S = SyntacticInfo
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure UF = UnionFind

  type id = int
  structure Map = IntRedBlackMap
  structure Set = IntRedBlackSet
  structure Tbl = IntHashTable

  datatype kind = User | Cont

  type info = {
    defs: LCPS.function vector,
    uses: LCPS.lvar vector,
    polluted: bool,
    kind: kind
  }

  datatype t = T of {
    webs: info vector,
    funMap: id LCPS.FunTbl.hash_table,
    varMap: id LV.Tbl.hash_table
  }

  datatype info'
    = Partial of {
        defs: LCPS.FunSet.set,
        uses: LV.Set.set,
        polluted: bool,
        kind: kind
      }
    | Standard of kind
    | Sealed of id

  fun timeit str f x =
    let
      val start = Time.now ()
      val result = f x
      val stop = Time.now ()
      val diff = Time.- (stop, start)
      val () = (print (str ^ " " ^ Time.toString diff); print "\n")
    in
      result
    end

  fun timeit _ f x = f x

  fun mergeInfo
    (Partial {defs=defs1, uses=uses1, polluted=polluted1, kind=kind1},
     Partial {defs=defs2, uses=uses2, polluted=polluted2, kind=kind2}) =
       let val kind = if kind1 <> kind2 then raise Fail "Ill-merge" else kind1
       (* Check: this is disjoint *)
           val defs = LCPS.FunSet.union (defs1, defs2)
           val uses = LV.Set.union (uses1, uses2)
           val polluted = polluted1 orelse polluted2
       in  Partial {defs=defs, uses=uses, polluted=polluted, kind=kind}
       end
    | mergeInfo (Partial _, Standard kind) = Standard kind
    | mergeInfo (Standard kind, Partial _) = Standard kind
    | mergeInfo _ = raise Fail "impossible"

  fun calculate ({lookup, flow} : FlowCFA.result, syn) =
    let val funTbl = LCPS.FunTbl.mkTable (S.numFuns syn, Fail "funmap")
        val varTbl = LV.Tbl.mkTable (S.numVars syn, Fail "varmap")

        val stdfunWeb =
          let
            (* val web = { defs=LCPS.FunSet.empty, uses=LV.Set.empty, *)
            (*               polluted=true, kind=User } *)
          in  UF.make (Standard User)
          end

        val stdcntWeb =
          let
            (* val web = { defs=LCPS.FunSet.empty, uses=LV.Set.empty, *)
            (*               polluted=true, kind=Cont } *)
          in  UF.make (Standard Cont)
          end

        fun addstdF (f, stdweb) =
          (case UF.get stdweb
             of Partial { defs, uses, polluted, kind } =>
                  let val defs = LCPS.FunSet.add (defs, f)
                      val web =
                        { defs=defs, uses=uses, polluted=polluted, kind=kind }
                  in  UF.set (stdweb, Partial web)
                  end
              | _ => raise Fail "impossible")

        fun addstdV (v, stdweb) =
          (case UF.get stdweb
             of Partial { defs, uses, polluted, kind } =>
                  let val uses = LV.Set.add (uses, v)
                      val web =
                        { defs=defs, uses=uses, polluted=polluted, kind=kind }
                  in  UF.set (stdweb, Partial web)
                  end
              | _ => raise Fail "impossible")


        fun mkSingleF (f, kind) : info' UF.elem =
          let val web = { defs=LCPS.FunSet.singleton f, uses=LV.Set.empty,
                          polluted=false, kind=kind }
              val elem = UF.make (Partial web)
          in  elem
          end

        fun mkSingleV (v, kind): info' UF.elem =
          let val web = { defs=LCPS.FunSet.empty, uses=LV.Set.singleton v,
                          polluted=false, kind=kind }
              val elem = UF.make (Partial web)
          in  elem
          end

        fun initF (f, {known, escape}: FlowCFA.variables)
          : info' UF.elem * LCPS.lvar list =
          let val (kind, stdweb) =
                (case #1 f of CPS.CONT => (Cont, stdcntWeb)
                            | _ => (User, stdfunWeb))
              val web =
                if escape then
                  stdweb
                else
                  mkSingleF (f, kind)
          in  LCPS.FunTbl.insert funTbl (f, web); (web, known)
          end

        fun initV (v, {known, unknown}: FlowCFA.functions)
          : info' UF.elem * LCPS.function list =
          let val (kind, stdweb) =
                (case S.typeof syn v
                   of CPS.CNTt => (Cont, stdcntWeb)
                    | _ => (User, stdfunWeb))
              val web =
                if unknown then
                  stdweb
                else
                  mkSingleV (v, kind)
          in  LV.Tbl.insert varTbl (v, web); (web, known)
          end

        val union = UF.merge mergeInfo

        fun hasFunTy v =
          (case S.typeof syn v
             of (CPS.CNTt | CPS.FUNt) => true
              | _ => false)

        val defaultW = { known=[], unknown=true } : FlowCFA.functions

        fun initialize () =
          let val fs = S.foldF syn (fn (f, acc) => initF (f, flow f) :: acc) []
              val vs = S.foldV syn (fn (v, acc) =>
                         (case lookup v
                            of NONE => if hasFunTy v then
                                         initV (v, defaultW) :: acc
                                       else
                                         acc
                             | SOME info => initV (v, info) :: acc)) []
          in  (fs, vs)
          end

        fun lookupF f = LCPS.FunTbl.lookup funTbl f
        fun lookupV v = LV.Tbl.lookup varTbl v
                        handle e => (print (LV.lvarName v ^ "\n"); raise e)
        fun lookupOrInitV v =
          (case LV.Tbl.find varTbl v
             of SOME cell => cell
              | NONE => #1 (initV (v, defaultW)))

        fun processF (fcell, known) =
          let val _ = foldl (fn (v, c) => union (lookupV v, c)) fcell known
          in  ()
          end

        fun processV (vcell, known) =
          let val _ = foldl (fn (f, c) => union (lookupF f, c)) vcell known
          in  ()
          end

        fun unionStd cell =
          (case UF.get cell
             of Sealed _ => raise Fail "unexpected sealed"
              | Partial { kind=User, ... } => ignore (union (cell, stdfunWeb))
              | Partial { kind=Cont, ... } => ignore (union (cell, stdcntWeb))
              | Standard _ => ())

        fun processCallConv (_, f, args) =
          let val f = (case f of CPS.VAR f => f | _ => raise Fail "call non-var")
              fun setStd args =
                app (fn (CPS.VAR v) =>
                        (case LV.Tbl.find varTbl v
                           of SOME cell => unionStd cell
                            | NONE => ())
                      | _ => ()) args
              fun align (formals, tys, actuals) =
                let fun go ([], [], []) = ()
                      | go (f :: formals, t :: tys, a :: actuals) =
                          (case (t, a)
                             of ((CPS.FUNt | CPS.CNTt), CPS.VAR a) =>
                                let val fcell = lookupV f
                                    val acell = lookupOrInitV a
                                in  union (fcell, acell);
                                    go (formals, tys, actuals)
                                end
                              | _ => ())
                      | go _ = raise ListPair.UnequalLengths
                in  go (formals, tys, actuals)
                end
          in  case lookup f
                of (NONE | SOME { unknown=true, ... })=> setStd args
                 | SOME { known, unknown=false } =>
                     app (fn (_, _, formals, tys, _) =>
                            align (formals, tys, args)) known
          end

        fun build (fs, vs) =
          (app processF fs; app processV vs; S.appApp syn processCallConv)

        fun finalize () =
          let fun convertWeb { defs, uses, polluted, kind } : info =
                { defs=Vector.fromList (LCPS.FunSet.listItems defs),
                  uses=Vector.fromList (LV.Set.listItems uses),
                  polluted=polluted,
                  kind=kind }

              fun collectF (f, cell, (currID, webs)) =
                (case UF.get cell
                   of Partial info =>
                        let val web = convertWeb info
                            val () = UF.set (cell, Sealed currID)
                        in  (currID + 1, web :: webs)
                        end
                    | _ => (currID, webs))

              fun collectV (v, cell, (currID, webs)) =
                (case UF.get cell
                   of Partial info =>
                        raise Fail
                          "webs without a function and does not escape????"
                    | _ => (currID, webs))

              fun removeCell cell =
                (case UF.get cell
                   of Partial _ => raise Fail "partial remaining"
                    | Standard _ => raise Fail "standard remaining"
                    | Sealed id => id)

              val web0 =
                (UF.set (stdfunWeb, Sealed 0);
                 { polluted=true, kind=User, defs= #[], uses= #[] })
                (* (case UF.get stdfunWeb *)
                (*    of Partial info => *)
                (*         let val web = convertWeb info *)
                (*             val () = UF.set (stdfunWeb, Sealed 0) *)
                (*         in  web *)
                (*         end *)
                (*     | _ => raise Fail "impossible") *)

              val web1 =
                (UF.set (stdcntWeb, Sealed 1);
                 { polluted=true, kind=Cont, defs= #[], uses= #[] })
                (* (case UF.get stdcntWeb *)
                (*    of Partial info => *)
                (*         let val web = convertWeb info *)
                (*             val () = UF.set (stdcntWeb, Sealed 1) *)
                (*         in  web *)
                (*         end *)
                (*     | _ => raise Fail "impossible") *)

              val (len, webs) =
                LCPS.FunTbl.foldi collectF (2, [web1, web0]) funTbl
              (* val (len, webs) = LV.Tbl.foldi collectV (len, webs) varTbl *)

              (* val () = if len <> List.length webs then raise Fail "len?" else () *)
          in  (Vector.fromList (List.rev webs),
               LCPS.FunTbl.map removeCell funTbl,
               LV.Tbl.map removeCell varTbl)
          end

        val (webs, funMap, varMap) =
          let val (fs, vs) = timeit "init" initialize ()
              val () = timeit "build" build (fs, vs);
          in  timeit "final" finalize ()
          end
    in  T { webs=webs, funMap=funMap, varMap=varMap }
    end

  fun webOfVar (T { varMap, ... }, v) = LV.Tbl.find varMap v
    (* (case LV.Tbl.find varMap v *)
    (*    of SOME w => w *)
    (*     | NONE => raise Fail ("No web info for " ^ LV.lvarName v)) *)

  fun webOfFun (T { funMap, ... }, f) =
    (case LCPS.FunTbl.find funMap f
       of SOME w => w
        | NONE => raise Fail ("No web info for " ^ LV.lvarName (#2 f)))

  fun content (T { webs, ... }, x) = Vector.sub (webs, x)

  fun mapL f vector = Vector.foldr (fn (v, xs) => f v :: xs) [] vector
  val _ = mapL : ('a -> 'b) -> 'a vector -> 'b list

  val defs = #defs o content
  val uses = #uses o content
  val polluted = #polluted o content
  val kind = #kind o content

  fun fold f zero (T { webs, funMap, varMap }) = Vector.foldli f zero webs

  fun kindOfCty CPS.CNTt = Cont
    | kindOfCty _ = User

  val idToString = Int.toString

  fun toString ({defs, uses, polluted, kind}: info) =
    let val fs = String.concatWith "," (mapL (LV.lvarName o #2) defs)
        val vs = String.concatWith "," (mapL LV.lvarName uses)
        val polluted = if polluted then " (polluted)" else ""
        val kind = case kind of User => "user" | Cont => "cont"
    in  concat [
          "Web ", kind, polluted, "\n",
          "  defs: [", fs, "]\n",
          "  uses: [", vs, "]\n"
        ]
    end

  fun webToS (id: int, { defs, uses, polluted, kind }: info) =
    let
        val fs = String.concatWith "," (mapL (LV.lvarName o #2) defs)
        val vs = String.concatWith "," (mapL LV.lvarName uses)
        (* val fs = Int.toString (Vector.length defs) *)
        (* val vs = Int.toString (Vector.length uses) *)
        val polluted = if polluted then " (polluted)" else ""
        val kind = case kind of User => "user" | Cont => "cont"
    in
        (* if Vector.length defs < 5 then "" else *)
        concat [
          "Web #", Int.toString id, " ", kind, polluted, "\n",
          "  defs: [", fs, "]\n",
          "  uses: [", vs, "]\n"
        ]
    end

  fun dump (T { webs, ... }) = Vector.appi (print o webToS) webs

end
