structure ClosureDecision = struct
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo

  structure EnvID :> sig
    type t

    val new : unit -> t
    val wrap : LV.lvar -> t
    val unwrap : t -> LV.lvar
    val toString : t -> string

    structure Map : ORD_MAP where type Key.ord_key = t
    structure Set : ORD_SET where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t
    structure MonoSet : MONO_HASH_SET where type Key.hash_key = t
  end = struct
    type t = LV.lvar

    val new = LV.mkLvar
    fun wrap x = x
    fun unwrap x = x
    val toString = LV.lvarName

    structure Map = LV.Map
    structure Set = LV.Set
    structure Tbl = LV.Tbl
    structure MonoSet = HashSetFn(LV.Tbl.Key)
  end

  datatype slot = EnvID  of EnvID.t
                | Var    of LV.lvar
                | Expand of LV.lvar * int
                | Code   of LV.lvar
                | Null

  datatype t = T of {
    repr: slot    list LCPS.FunMap.map,
    allo: EnvID.t list Group.Map.map,
    heap: slot    list EnvID.Map.map
  }

  fun slotToString (Var v) = concat ["[V]", LV.lvarName v]
    | slotToString (Code c) = concat ["[L]", LV.lvarName c]
    | slotToString (Expand (v, i)) =
        concat ["[CS]", LV.lvarName v, "#", Int.toString i]
    | slotToString Null = "Null"
    | slotToString (EnvID e) = concat ["[E]", EnvID.toString e]

  fun dump (T { repr, allo, heap }, syn) =
    let
      val p = app print
      val cwm = String.concatWithMap
      val tyToS = CPSUtil.ctyToString
      fun printSlot (indent, slot, printed) =
        (case slot
           of Var v  => p [indent, "Var ", LV.lvarName v,
                           tyToS (S.typeof syn v), "\n"]
            | Code c => p [indent, "Lab ", LV.lvarName c, "\n"]
            | Expand (v, i) => p [indent, "Expand #", Int.toString i, " of ",
                                  LV.lvarName v, "\n"]
            | Null   => p [indent, "Null\n"]
            | EnvID e =>
                (p [indent, "Env ", EnvID.toString e, ":"];
                 if EnvID.MonoSet.member (printed, e) then
                   p [" <seen>\n"]
                 else (
                   p ["\n"];
                   EnvID.MonoSet.add (printed, e);
                   printEnv ("  " ^ indent, EnvID.Map.lookup (heap, e),
                             printed))))
      and printEnv (indent, slots, printed) =
        app (fn s => printSlot (indent, s, printed)) slots

      fun kindToS CPS.CONT = "std_cont"
        | kindToS CPS.KNOWN = "known"
        | kindToS CPS.KNOWN_REC = "known_rec"
        | kindToS CPS.KNOWN_CHECK = "known_chk"
        | kindToS CPS.KNOWN_TAIL = "known_tail"
        | kindToS CPS.KNOWN_CONT = "known_cont"
        | kindToS CPS.ESCAPE = "std"
        | kindToS CPS.NO_INLINE_INTO = "noinline"

      fun funname ((kind, name, _, _, _): LCPS.function) =
        concat [LV.lvarName name, "(", kindToS kind, ")"]

      fun printGroup group =
        let val functions = Vector.toList (S.groupFun syn group)
            val () = p ["Group [", cwm "," funname functions, "]:\n"]
            val printed = EnvID.MonoSet.mkEmpty 8
            val alloc = Option.getOpt (Group.Map.find (allo, group), [])
            val () = p ["  Allocating: [", cwm "," EnvID.toString alloc, "]\n"]
            val () = app (fn f =>
              let val slots = LCPS.FunMap.lookup (repr, f)
              in  p ["  ", LV.lvarName (#2 f), " represented as [",
                     cwm "," slotToString slots, "]:\n"];
                  printEnv ("    ", slots, printed)
              end) functions
        in  ()
        end
    in
      Vector.app printGroup (S.groups syn)
    end
end
