structure DotLanguage :> sig
  type attr = string * string
  type id   = string
  datatype stmt
    = NODE of id * attr list
    | EDGE of id * id * attr list
    | ATTR of string
    | SUBGRAPH of id option * stmt list
  type t

  val empty : bool * string -> t
  val <<  : t * stmt -> t
  val <+< : t * stmt list -> t
  val dump : t -> unit
  val toString : t -> string
  val write : string -> t -> unit
  val fromGraph : ('node -> id * attr list)
               -> { roots: 'node list, follow: 'node -> 'node list }
               -> t
end = struct
  type attr = string * string
  type id   = string
  datatype stmt
    = NODE of id * attr list
    | EDGE of id * id * attr list
    | ATTR of string
    | SUBGRAPH of id option * stmt list

  type t = { directed : bool
           , name     : string
           , stmts    : stmt list
           }

  fun s str      = "\"" ^ (String.toString str) ^ "\""
  val concatWith = String.concatWith
  val map        = List.map

  fun stringOfAttr (k, v) = k ^ "=" ^ (s v)

  fun stringOfAttrs []    = ""
    | stringOfAttrs attrs =
        "[" ^ (concatWith "; " (map stringOfAttr attrs)) ^ "]"

  fun quote s = "\"" ^ s ^ "\""

  fun stringOfStmt edgeShape (NODE (name, attrs)) =
        quote name ^ " " ^ (stringOfAttrs attrs)
    | stringOfStmt edgeShape (EDGE (from, to, attrs)) =
        quote from ^ " " ^ edgeShape ^ " " ^ quote to ^ " " ^ (stringOfAttrs attrs)
    | stringOfStmt edgeShape (ATTR attr) = attr
    | stringOfStmt edgeShape (SUBGRAPH (opt, stmts)) =
        "subgraph " ^ (case opt of NONE => "" | SOME id => s id) ^ " {\n"
                    ^ (concatWith "\n" (map (stringOfStmt edgeShape) stmts))
                    ^ "\n}"

  fun stringOf {directed, name, stmts} =
    let val graphType = if directed then "digraph" else "graph"
        val name      = if String.size name = 0 then "" else s name
        val edgeShape = if directed then "->" else "--"
    in  graphType ^ " " ^ name ^ " {\n"
        ^ (concatWith "\n" (map (stringOfStmt edgeShape) stmts))
        ^ "\n}\n"
    end

  val toString = stringOf

  fun write filename d = TextIO.output (TextIO.openOut filename, stringOf d)

  val dump = print o stringOf

  fun empty (directed, name) : t = {directed=directed, name=name, stmts=[]}

  infix 3 <<
  fun {directed, name, stmts} << stmt =
    {directed=directed, name=name, stmts=stmts @ [stmt]}

  infix 3 <+<
  fun {directed, name, stmts} <+< stmt =
    {directed=directed, name=name, stmts=stmts @ stmt}

  fun fromGraph convert {roots, follow} =
    let
      fun dfs seen [] doc = doc
        | dfs seen (node::todo) doc =
            let val n as (name, _) = convert node
                val name' = Atom.atom name
            in  if AtomSet.member (seen, name') then
                  dfs seen todo doc
                else
                  let
                    val seen' = AtomSet.add (seen, name')
                    val nexts = follow node
                    val names = map (#1 o convert) nexts
                    val doc' =
                      doc <+<
                        (NODE n :: map (fn n' => EDGE (name, n', [])) names)
                  in
                    dfs seen' (nexts @ todo) doc'
                  end
            end
    in
      dfs AtomSet.empty roots (empty (true, "call-graph"))
    end
end
