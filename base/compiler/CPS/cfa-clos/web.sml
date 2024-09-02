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

  datatype either = datatype Either.either

  fun calculate ({lookup, flow} : FlowCFA.result, syn) =
    let
      type item = (LCPS.lvar, LCPS.function) either

      val funMap = LCPS.FunTbl.mkTable (S.numFuns syn, Fail "funmap")
      val varMap = LV.Tbl.mkTable (S.numVars syn, Fail "varmap")

      fun maximize ([], id, defs, uses, polluted) = (defs, uses, polluted)
        | maximize (INL v :: todo', id, defs, uses, polluted) =
            if LV.Set.member (uses, v) then
              maximize (todo', id, defs, uses, polluted)
            else
              (case lookup v
                 of NONE => (* v is dead, can this even be possible? *)
                      raise Fail "Impossible dead variable in a web"
                  | SOME { known, unknown } =>
                      let val uses = LV.Set.add (uses, v)
                          val () = LV.Tbl.insert varMap (v, id)
                          val () =
                          (case LV.Tbl.find varMap v
                             of SOME _ => raise Fail "Double v"
                              | NONE => ())
                          val polluted = polluted orelse unknown
                      in  maximize (map INR known @ todo',
                                    id, defs, uses, polluted)
                      end)
        | maximize (INR f :: todo', id, defs, uses, polluted) =
            if LCPS.FunSet.member (defs, f) then
              maximize (todo', id, defs, uses, polluted)
            else
              let val { known, escape } = flow f
                  val defs = LCPS.FunSet.add (defs, f)
                  val () =
                  (case LCPS.FunTbl.find funMap f
                     of SOME _ => raise Fail "Double f"
                      | NONE => ())
                  val () = LCPS.FunTbl.insert funMap (f, id)
                  val polluted = polluted orelse escape
              in  maximize (map INL known @ todo', id, defs, uses, polluted)
              end

      fun processFun (f, (length, webs: info list)) =
        if LCPS.FunTbl.inDomain funMap f then
          (length, webs)
        else
          let val id = length
              val web as (defs, uses, polluted) =
                maximize ([INR f], id, LCPS.FunSet.empty, LV.Set.empty, false)
              val defs = LCPS.FunSet.toList defs and uses = LV.Set.toList uses
              val kind =
                (case #1 (List.hd defs) of CPS.CONT => Cont | _ => User)
              val web = { defs=Vector.fromList defs, uses=Vector.fromList uses,
                          polluted=polluted, kind=kind }
          in  (length + 1, web :: webs)
          end

      datatype state
        = Known of {
            defs: LCPS.FunSet.set,
            uses: LV.Set.set,
            std: { defs: LCPS.FunSet.set, uses: LV.Set.set }
          }
        | Std of { defs: LCPS.FunSet.set, uses: LV.Set.set }

      fun maximize ([], state) = state
        | maximize (INL v :: todo', st as Known { defs, uses, std }) =
            if LV.Set.member (uses, v) then
              maximize (todo', st)
            else
              (case lookup v
                 of NONE => (* v is dead, can this even be possible? *)
                      raise Fail "Impossible dead variable in a web"
                  | SOME { known, unknown } =>
                      if unknown then (* switching state now *)
                        let val { defs=stdDefs, uses=stdUses } = std
                            val stdDefs = LCPS.FunSet.union (defs, stdDefs)
                            val stdUses = LV.Set.union (uses, stdUses)
                            val stdUses = LV.Set.add (stdUses, v)
                        in  maximize (map INR known @ todo',
                                      Std { defs=stdDefs, uses=stdUses })
                        end
                      else (* staying known *)
                        let val uses = LV.Set.add (uses, v)
                        in  maximize (map INR known @ todo',
                                      Known { defs=defs, uses=uses, std=std })
                        end)
        | maximize (INR f :: todo', st as Known { defs, uses, std }) =
            if LCPS.FunSet.member (defs, f) then
              maximize (todo', st)
            else
              let val { known, escape } = flow f
              in  if escape then (* switching state *)
                    let val { defs=stdDefs, uses=stdUses } = std
                        val stdDefs = LCPS.FunSet.union (defs, stdDefs)
                        val stdUses = LV.Set.union (uses, stdUses)
                        val stdDefs = LCPS.FunSet.add (stdDefs, f)
                    in  maximize (map INL known @ todo',
                                  Std { defs=stdDefs, uses=stdUses })
                    end
                  else
                    let val defs = LCPS.FunSet.add (defs, f)
                    in  maximize (map INL known @ todo',
                                  Known { defs=defs, uses=uses, std=std })
                    end
              end
        | maximize (INL v :: todo', st as Std { defs, uses }) =
            if LV.Set.member (uses, v) then
              maximize (todo', st)
            else
              (case lookup v
                 of NONE => raise Fail "Impossible dead variable in a web"
                  | SOME { known, unknown } =>
                      let val uses = LV.Set.add (uses, v)
                      in  maximize (map INR known @ todo',
                                    Std { defs=defs, uses=uses })
                      end)
        | maximize (INR f :: todo', st as Std { defs, uses }) =
            if LCPS.FunSet.member (defs, f) then
              maximize (todo', st)
            else
              let val { known, escape } = flow f
                  val defs = LCPS.FunSet.add (defs, f)
              in  maximize (map INL known @ todo', Std { defs=defs, uses=uses })
              end

      fun addIdF id f =
        (* (if Option.isSome (LCPS.FunTbl.find funMap f) then *)
        (*    raise Fail "Double f" *)
        (*  else *)
        (*    (); *)
         LCPS.FunTbl.insert funMap (f, id)
      fun addIdV id v =
        (* (if Option.isSome (LV.Tbl.find varMap v) then *)
        (*    raise Fail "Double v" *)
        (*  else *)
        (*    (); *)
         LV.Tbl.insert varMap (v, id)

      fun toWeb (id, defs, uses, polluted, kind): info =
        let val defs = LCPS.FunSet.listItems defs
            val uses = LV.Set.listItems uses
            val () = List.app (addIdF id) defs
            val () = List.app (addIdV id) uses
        in  { defs=Vector.fromList defs, uses=Vector.fromList uses,
              polluted=polluted, kind=kind }
        end

      fun processFun (f, (length, webs: info list, stdfun, stdcnt))=
        (case #1 f
           of CPS.CONT =>
                if LCPS.FunTbl.inDomain funMap f
                   orelse LCPS.FunSet.member (#defs stdcnt, f) then
                  (length, webs, stdfun, stdcnt)
                else
                  (case maximize ([INR f],
                                  Known { defs=LCPS.FunSet.empty,
                                          uses=LV.Set.empty,
                                          std=stdcnt })
                     of Known { defs, uses, std } =>
                          let val web = toWeb (length, defs, uses, false, Cont)
                          handle e => raise e
                          in  (length + 1, web :: webs, stdfun, stdcnt)
                          end
                      | Std { defs, uses } =>
                          (length, webs, stdfun, { defs=defs, uses=uses }))
            | _ =>
                if LCPS.FunTbl.inDomain funMap f
                   orelse LCPS.FunSet.member (#defs stdfun, f) then
                  (length, webs, stdfun, stdcnt)
                else
                  (case maximize ([INR f],
                                  Known { defs=LCPS.FunSet.empty,
                                          uses=LV.Set.empty,
                                          std=stdfun })
                     of Known { defs, uses, std } =>
                          let val web = toWeb (length, defs, uses, false, User)
                          handle e => raise e
                          in  (length + 1, web :: webs, stdfun, stdcnt)
                          end
                      | Std { defs, uses } =>
                          (length, webs, { defs=defs, uses=uses }, stdcnt)))
      (* Web #0 is stdfun, Web #1 is stdcnt *)
      val (length, webs, stdfun, stdcnt) =
        Vector.foldl
          processFun
          (2, [], { defs=LCPS.FunSet.empty, uses=LV.Set.empty },
                  { defs=LCPS.FunSet.empty, uses=LV.Set.empty })
          (S.functions syn)
      val stdfun = toWeb (0, #defs stdfun, #uses stdfun, true, User)
      handle e => raise e
      val stdcnt = toWeb (1, #defs stdcnt, #uses stdcnt, true, Cont)
      handle e => raise e
      val webs = Vector.fromList (stdfun :: stdcnt :: List.rev webs)
      (* val (length, webs) = Vector.foldl processFun (0, []) (S.functions syn) *)
      (* val webs = Vector.fromList (List.rev webs) *)
    in
      T { webs=webs, funMap=funMap, varMap=varMap }
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
