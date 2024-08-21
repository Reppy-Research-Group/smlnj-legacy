structure Web :> sig
  type id
  type t

  val calculate : FlowCFA.result * SyntacticInfo.t -> t

  val webOfVar : t * LabelledCPS.lvar -> id option
  val webOfFun : t * LabelledCPS.function -> id

  datatype kind = User | Cont

  val defs : t * id -> LabelledCPS.function vector
  val uses : t * id -> LabelledCPS.lvar vector
  val content : t * id -> { defs: LabelledCPS.function vector,
                            uses: LabelledCPS.lvar vector,
                            polluted: bool,
                            kind: kind }
  val polluted : t * id -> bool
  val kind : t * id -> kind
  val kindOfCty : CPS.cty -> kind

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

      fun maximize ([], defs, uses, polluted) = (defs, uses, polluted)
        | maximize (INL v :: todo', defs, uses, polluted) =
            if LV.Set.member (uses, v) then
              maximize (todo', defs, uses, polluted)
            else
              (case lookup v
                 of NONE => (* v is dead, can this even be possible? *)
                      raise Fail "Impossible dead variable in a web"
                  | SOME { known, unknown } =>
                      let val uses = LV.Set.add (uses, v)
                          val polluted = polluted orelse unknown
                      in  maximize (map INR known @ todo', defs, uses, polluted)
                      end)
        | maximize (INR f :: todo', defs, uses, polluted) =
            if LCPS.FunSet.member (defs, f) then
              maximize (todo', defs, uses, polluted)
            else
              let val { known, escape } = flow f
                  val defs = LCPS.FunSet.add (defs, f)
                  val polluted = polluted orelse escape
              in  maximize (map INL known @ todo', defs, uses, polluted)
              end

      val funMap = LCPS.FunTbl.mkTable (1024, Fail "funmap")
      val varMap = LV.Tbl.mkTable (1024, Fail "varmap")

      fun processFun (f, (length, webs: info list)) =
        if LCPS.FunTbl.inDomain funMap f then
          (length, webs)
        else
          let val web as (defs, uses, polluted) =
                maximize ([INR f], LCPS.FunSet.empty, LV.Set.empty, false)
              val defs = LCPS.FunSet.toList defs and uses = LV.Set.toList uses
              val kind =
                (case #1 (List.hd defs)
                   of (CPS.CONT | CPS.KNOWN_CONT) => Cont
                    | _ => User)
              val id = length
              val () = List.app (fn f => LCPS.FunTbl.insert funMap (f, id)) defs
              val () = List.app (fn v => LV.Tbl.insert varMap (v, id)) uses
              val web = { defs=Vector.fromList defs, uses=Vector.fromList uses,
                          polluted=polluted, kind=kind }
          in  (length + 1, web :: webs)
          end
      val (length, webs) = Vector.foldl processFun (0, []) (S.functions syn)
      val webs = Vector.fromList (List.rev webs)
    in
      T {
        webs=webs,
        funMap=funMap,
        varMap=varMap
      }
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

  fun kindOfCty CPS.CNTt = Cont
    | kindOfCty _ = User

  fun webToS (id: int, { defs, uses, polluted, kind }: info) =
    let val fs = String.concatWith "," (mapL (LV.lvarName o #2) defs)
        val vs = String.concatWith "," (mapL LV.lvarName uses)
        val polluted = if polluted then " (polluted)" else ""
        val kind = case kind of User => "user" | Cont => "cont"
    in  concat [
          "Web #", Int.toString id, " ", kind, polluted, "\n",
          "  defs: [", fs, "]\n",
          "  uses: [", vs, "]\n"
        ]
    end

  fun dump (T { webs, ... }) = Vector.appi (print o webToS) webs

end
