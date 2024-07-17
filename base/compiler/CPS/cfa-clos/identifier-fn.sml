(* identifier-fn.sml
 *)

functor IdentifierFn () : sig

    type t

    (* define a new variable with the given name *)
    val new : string -> t

    (* the source-code name of the identifier *)
    val nameOf : t -> string
    (* a unique string representation of the identifier *)
    val toString : t -> string

    (* comparisons *)
    val compare : t * t -> order
    val same : t * t -> bool

    (* finite sets of identifiers *)
    structure Set : ORD_SET where type Key.ord_key = t
    (* finite maps with identifier keys *)
    structure Map : ORD_MAP where type Key.ord_key = t
    (* hash tables with identifier keys *)
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    datatype t = ID of {
        name : string,
        stamp : int
      }

    local
      val counter = ref 0
    in
      fun alloc () = !counter before counter := !counter + 1
    end

    fun new name = ID{
            name = name,
            stamp = alloc ()
          }

    fun nameOf (ID{name, ...}) = name

    fun toString (ID{name, stamp, ...}) = name ^ Int.toString stamp

    fun compare (ID{stamp = id1, ...}, ID{stamp = id2, ...}) = Int.compare(id1, id2)

    fun same (ID{stamp = id1, ...}, ID{stamp = id2, ...}) = id1 = id2

    structure Set = RedBlackSetFn (
      struct
        type ord_key = t
        val compare = compare
      end)
    structure Map = RedBlackMapFn (
      struct
        type ord_key = t
        val compare = compare
      end)
    structure Tbl = HashTableFn (
      struct
        type hash_key = t
        fun hashVal (ID{stamp, ...}) = Word.fromInt stamp
        val sameKey = same
      end)

  end

