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
    | mergeInfo _ = raise Fail "impossible"

  fun calculate ({lookup, flow} : FlowCFA.result, syn) =
    let val funTbl = LCPS.FunTbl.mkTable (S.numFuns syn, Fail "funmap")
        val varTbl = LV.Tbl.mkTable (S.numVars syn, Fail "varmap")

        (* TODO: specialize *)
        val stdfunWeb =
          let val web = { defs=LCPS.FunSet.empty, uses=LV.Set.empty,
                          polluted=true, kind=User }
          in  UF.make (Partial web)
          end

        val stdcntWeb =
          let val web = { defs=LCPS.FunSet.empty, uses=LV.Set.empty,
                          polluted=true, kind=Cont }
          in  UF.make (Partial web)
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

        fun initF (f, flowInfo: FlowCFA.variables) : unit =
          let val (kind, stdweb) =
                (case #1 f of CPS.CONT => (Cont, stdcntWeb)
                            | _ => (User, stdfunWeb))
              val web =
                if #escape flowInfo then
                  (addstdF (f, stdweb); stdweb)
                else
                  mkSingleF (f, kind)
          in  LCPS.FunTbl.insert funTbl (f, web)
          end

        fun initV (v, flowInfo: FlowCFA.functions) : unit =
          let val (kind, stdweb) =
                (case S.typeof syn v
                   of CPS.CNTt => (Cont, stdcntWeb)
                    | _ => (User, stdfunWeb))
              val web =
                if #unknown flowInfo then
                  (addstdV (v, stdweb); stdweb)
                else
                  mkSingleV (v, kind)
          in  LV.Tbl.insert varTbl (v, web)
          end

        val union = UF.merge mergeInfo

        fun initialize () =
          (S.appF syn (fn f => initF (f, flow f));
           S.appV syn (fn v => (case lookup v
                                  of NONE => ()
                                   | SOME info => initV (v, info))))

        fun lookupF f = LCPS.FunTbl.lookup funTbl f
        fun lookupV v = LV.Tbl.lookup varTbl v

        fun processF f =
          let val { known, escape } = flow f
              val fcell = lookupF f
              val _ = foldl (fn (v, c) => union (lookupV v, c)) fcell known
          in  ()
          end

        fun processV v =
          (case lookup v
             of SOME { known, unknown } =>
                  let val vcell = lookupV v
                      val _ =
                        foldl (fn (f, c) => union (lookupF f, c)) vcell known
                  in  ()
                  end
              | NONE => ())

        fun build () = (S.appF syn processF; S.appV syn processV)

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
                    | Sealed _ => (currID, webs))

              fun collectV (v, cell, (currID, webs)) =
                (case UF.get cell
                   of Partial info =>
                        raise Fail
                          "webs without a function and does not escape????"
                    | Sealed _ => (currID, webs))

              fun removeCell cell =
                (case UF.get cell
                   of Partial _ => raise Fail "partial remaining"
                    | Sealed id => id)

              val web0 =
                (case UF.get stdfunWeb
                   of Partial info =>
                        let val web = convertWeb info
                            val () = UF.set (stdfunWeb, Sealed 0)
                        in  web
                        end
                    | _ => raise Fail "impossible")

              val web1 =
                (case UF.get stdcntWeb
                   of Partial info =>
                        let val web = convertWeb info
                            val () = UF.set (stdcntWeb, Sealed 1)
                        in  web
                        end
                    | _ => raise Fail "impossible")

              val (len, webs) =
                LCPS.FunTbl.foldi collectF (2, [web1, web0]) funTbl
              (* val (len, webs) = LV.Tbl.foldi collectV (len, webs) varTbl *)

              (* val () = if len <> List.length webs then raise Fail "len?" else () *)
          in  (Vector.fromList (List.rev webs),
               LCPS.FunTbl.map removeCell funTbl,
               LV.Tbl.map removeCell varTbl)
          end

        val (webs, funMap, varMap) = (initialize (); build (); finalize ())
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
