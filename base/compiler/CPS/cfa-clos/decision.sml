structure ClosureDecision = struct
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo

  structure EnvID :> sig
    type t

    val new : unit -> t
    val wrap : LV.lvar -> t
    val unwrap : t -> LV.lvar
    val dup    : t -> t
    val toString : t -> string
    val compare : t * t -> order
    val same : t * t -> bool

    structure Map : ORD_MAP where type Key.ord_key = t
    structure Set : ORD_SET where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t
    structure MonoSet : MONO_HASH_SET where type Key.hash_key = t
  end = struct
    type t = LV.lvar

    val new = LV.mkLvar
    val wrap = Fn.id
    val unwrap = Fn.id
    val toString = LV.lvarName
    val dup = LV.dupLvar
    val compare = LV.compare
    val same = LV.same

    structure Map = LV.Map
    structure Set = LV.Set
    structure Tbl = LV.Tbl
    structure MonoSet = HashSetFn(LV.Tbl.Key)
  end

  (* datatype convention = Boxed of EnvID.t *)
  (*                     | Flat  of LV.lvar * slot list *)
  (*
   * 2 x 3 situations
   * Code:
   *  - No need: whenever the function is called, it is the only function
   *  - Pointer
   *  - Defun (future)
   *
   * Environment:
   *  - Boxed
   *  - Flat
   *  - No environment
   *
   * - No code, boxed environment:
   *   f replaced with envid --> { fvs }
   * - No code, flat environment:
   *   f replaced with slots
   * - No code, no environment:
   *   remove (arity is 0)
   *
   * - Pointer/defun, boxed environment
   *   f replaced with envid --> {f @ fvs}
   * - Pointer/defun, flat environment:
   *   f replaced with f and slots
   * - Pointer/defun, no environment:
   *   f replaced with f
   *
   * Protocol:
   * - A template describing the ``type'' of the closure representation.
   *   { code: Pointer, Defun, Omitted, slot: cty list }
   *)

  datatype slot = EnvID  of EnvID.t
                | Var    of LV.lvar * CPS.cty
                | Expand of LV.lvar * int * CPS.cty
                | Code   of LCPS.function
                | Null

  datatype object = Record   of slot list * bool (* shared *)
                  | RawBlock of LV.lvar list * CPS.record_kind

  datatype code = Direct of LCPS.function
                | Pointer of LCPS.lvar
                | SelectFrom of { env: int, selects: int list }
                | Defun of LCPS.lvar * LCPS.function list

  datatype environment = Boxed of EnvID.t (* FIXME: remove this *)
                       | Flat  of slot list

  datatype closure = Closure of { code: code, env: environment }

  type repr = closure      LCPS.FunMap.map
  type allo = EnvID.t list Group.Map.map
  type heap = object       EnvID.Map.map

  datatype t = T of { repr: repr, allo: allo, heap: heap }

  fun slotToString (Var (v, ty)) =
        concat ["[V(", CPSUtil.ctyToString ty, ")]", LV.lvarName v]
    | slotToString (Code c) = concat ["[L]", LV.lvarName (#2 c)]
    | slotToString (Expand (v, i, ty)) =
        concat ["[CS(", CPSUtil.ctyToString ty, ")]", LV.lvarName v,
                "#", Int.toString i]
    | slotToString Null = "Null"
    | slotToString (EnvID e) = concat ["[E]", EnvID.toString e]

  fun codeToS (Direct f) = LV.lvarName (#2 f)
    | codeToS (Pointer v) = concat ["(*", LV.lvarName v, ")"]
    | codeToS (SelectFrom {env, selects}) =
        concat ["(*", Int.toString env, ".",
                String.concatWithMap "." Int.toString selects, ")"]
    | codeToS (Defun (v, fs)) = concat ["#", LV.lvarName v]

  fun envToS (Boxed e) = EnvID.toString e
    | envToS (Flat slots) = String.concatWithMap "," slotToString slots ^ ","

  fun envToSlots (Boxed e) = [EnvID e]
    | envToSlots (Flat slots) = slots

  fun compareSlot (EnvID e1, EnvID e2) = EnvID.compare (e1, e2)
    | compareSlot (EnvID _, _) = GREATER
    | compareSlot (_, EnvID _) = LESS
    | compareSlot (Var (v1, _), Var (v2, _)) = LV.compare (v1, v2)
    | compareSlot (Var _, _) = GREATER
    | compareSlot (_, Var _) = LESS
    | compareSlot (Expand (v1, i1, _), Expand (v2, i2, _)) =
        (case LV.compare (v1, v2)
           of EQUAL => Int.compare (i1, i2)
            | order => order)
    | compareSlot (Expand _, _) = GREATER
    | compareSlot (_, Expand _) = LESS
    | compareSlot (Code (_, name1, _, _, _), Code (_, name2, _, _, _)) =
        LV.compare (name1, name2)
    | compareSlot (Code _, _) = GREATER
    | compareSlot (_, Code _) = LESS
    | compareSlot (Null, Null) = EQUAL

  structure SlotKey : ORD_KEY = struct
    type ord_key = slot
    val compare = compareSlot
  end

  structure SlotSet = RedBlackSetFn(SlotKey)
  structure SlotMap = RedBlackMapFn(SlotKey)

  fun closureToS (Closure {code, env}) =
    concat [codeToS code, "(", envToS env, "...)"]

  fun dump (T { repr, allo, heap }, syn) =
    let
      val p = app print
      val cwm = String.concatWithMap
      val tyToS = CPSUtil.ctyToString
      fun printSlot (indent, slot, printed) =
        (case slot
           of Var (v, ty) => p [indent, "Var ", LV.lvarName v, tyToS ty, "\n"]
            | Code c => p [indent, "Lab ", LV.lvarName (#2 c), "\n"]
            | Expand (v, i, ty) =>
                p [indent, "Expand #", Int.toString i, " of ", LV.lvarName v,
                   "(", tyToS ty, ")\n"]
            | Null   => p [indent, "Null\n"]
            | EnvID e =>
                (p [indent, "Env ", EnvID.toString e, ":"];
                 if EnvID.MonoSet.member (printed, e) then
                   p [" <seen>\n"]
                 else (
                   p ["\n"];
                   EnvID.MonoSet.add (printed, e);
                   printObject ("  " ^ indent, EnvID.Map.lookup (heap, e),
                                printed))))
      and printSlots (indent, slots, printed) =
        app (fn s => printSlot (indent, s, printed)) slots
      and printObject (indent, obj, printed) =
        (case obj
           of Record (slots, shared) => 
                (print (if shared then "<shared>\n" else "<private>\n");
                 printSlots ("  " ^ indent, slots, printed))
            | RawBlock (vs, _) =>
                (p [indent, "RawBlock: "];
                 app (fn v => p [LV.lvarName v, " "]) vs))

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
              let val cl as Closure { env, ... } = LCPS.FunMap.lookup (repr, f)
              in  p ["  ", LV.lvarName (#2 f), " represented as ",
                     closureToS cl, ":\n"];
                  printSlots ("    ", envToSlots env, printed)
              end) functions
        in  ()
        end
    in
      Vector.app printGroup (S.groups syn)
    end
  fun dumpOne (T { repr, allo, heap }, syn, grp) =
    let
      val p = app print
      val cwm = String.concatWithMap
      val tyToS = CPSUtil.ctyToString
      fun printSlot (indent, slot, printed) =
        (case slot
           of Var (v, ty) => p [indent, "Var ", LV.lvarName v, tyToS ty, "\n"]
            | Code c => p [indent, "Lab ", LV.lvarName (#2 c), "\n"]
            | Expand (v, i, ty) =>
                p [indent, "Expand #", Int.toString i, " of ", LV.lvarName v,
                   "(", tyToS ty, ")\n"]
            | Null   => p [indent, "Null\n"]
            | EnvID e =>
                (p [indent, "Env ", EnvID.toString e, ":"];
                 if EnvID.MonoSet.member (printed, e) then
                   p [" <seen>\n"]
                 else (
                   p ["\n"];
                   EnvID.MonoSet.add (printed, e);
                   printObject ("  " ^ indent, EnvID.Map.lookup (heap, e),
                                printed))))
      and printSlots (indent, slots, printed) =
        app (fn s => printSlot (indent, s, printed)) slots
      and printObject (indent, obj, printed) =
        (case obj
           of Record (slots, shared) => 
                (print (if shared then "<shared>\n" else "<private>\n");
                 printSlots ("  " ^ indent, slots, printed))
            | RawBlock (vs, _) =>
                (p [indent, "RawBlock:\n"];
                 app (fn v => p ["  ", indent, LV.lvarName v, "\n"]) vs))

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
              let val cl as Closure { env, ... } = LCPS.FunMap.lookup (repr, f)
              in  p ["  ", LV.lvarName (#2 f), " represented as ",
                     closureToS cl, ":\n"];
                  printSlots ("    ", envToSlots env, printed)
              end) functions
        in  ()
        end
    in
      printGroup grp
    end
end
