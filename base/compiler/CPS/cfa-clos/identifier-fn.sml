(* identifier-fn.sml
 *)

functor IdentifierFn ( ) : sig

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

    (* properties *)
    val newFlag : unit -> {
            getFn : t -> bool,
            setFn : t * bool -> unit
          }

    val newProp : (t -> 'prop) -> {
            peekFn : t -> 'prop option,
            getFn  : t -> 'prop,
            setFn  : t * 'prop -> unit,
            clrFn  : t -> unit
          }

    (* finite sets of identifiers *)
    structure Set : ORD_SET where type Key.ord_key = t
    (* finite maps with identifier keys *)
    structure Map : ORD_MAP where type Key.ord_key = t
    (* hash tables with identifier keys *)
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    datatype t = ID of {
        name : string,
        stamp : int,
        props : PropList.holder
      }

    local
      val counter = ref 0
    in
      fun alloc () = !counter before counter := !counter + 1
    end

    fun new name = ID{
            name = name,
            stamp = alloc (),
            props = PropList.newHolder()
          }

    fun nameOf (ID{name, ...}) = name

    fun toString (ID{name, stamp, ...}) = name ^ Int.toString stamp

    fun compare (ID{stamp = id1, ...}, ID{stamp = id2, ...}) = Int.compare(id1, id2)

    fun same (ID{stamp = id1, ...}, ID{stamp = id2, ...}) = id1 = id2

    fun newFlag () = PropList.newFlag (fn (ID{props, ...}) => props)

    fun newProp initialize = PropList.newProp (
          fn (ID{props, ...}) => props,
          initialize)

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

