structure UnionFind :> sig
  type 'a elem

  val make : 'a -> 'a elem
  val get : 'a elem -> 'a
  val set : 'a elem * 'a -> unit
  val eq  : 'a elem * 'a elem -> bool
  val union : 'a elem * 'a elem -> 'a elem
  val merge : ('a * 'a -> 'a) -> 'a elem * 'a elem -> 'a elem
  val find : 'a elem -> 'a elem
  val isRepresentative : 'a elem -> bool
end = struct
  type rank = int

  datatype 'a content = Link of { parent: 'a elem }
                      | Root of { rank: rank, value: 'a }
  withtype 'a elem = 'a content ref

  fun make (v: 'a): 'a elem = ref (Root { rank=0, value=v })

  fun find (x as ref (Root _)) = x
    | find (x as ref (Link { parent=y })) =
        let val z = find y
        in  if z <> y then x := Link { parent=z } else (); z
        end

  fun isRepresentative (ref (Link _)) = true
    | isRepresentative (ref (Root _)) = false

  fun eq (x: 'a elem, y: 'a elem) : bool = x = y orelse find x = find y

  fun get (x: 'a elem) : 'a =
    let val ref x = find x
    in  case x
          of Root { value, ... } => value
           | Link _ => raise Fail "impossible"
    end

  fun set (x: 'a elem, v: 'a) : unit =
    let val x = find x
    in  case !x
          of Root { value, rank } => x := Root { value=v, rank=rank }
           | Link _ => raise Fail "impossible"
    end

  fun union (x: 'a elem, y: 'a elem) : 'a elem =
    let val x = find x
        val y = find y
    in  if x = y then
          x
        else
          case (!x, !y)
            of (Root { rank=rx, value=vx }, Root { rank=ry, value=vy })=>
                 if rx < ry then
                   (x := Link { parent=y }; y)
                 else if rx > ry then
                   (y := Link { parent=x }; x)
                 else
                   (y := Link { parent=x };
                    x := Root { rank=rx + 1, value=vx };
                    x)
             | _ => raise Fail "impossible"
    end

  fun merge (f: 'a * 'a -> 'a) (x: 'a elem, y: 'a elem) : 'a elem =
    let val x = find x
        val y = find y
    in  if x = y then
          x
        else
          case (!x, !y)
            of (Root { rank=rx, value=vx },
                Root { rank=ry, value=vy })=>
                let val v = f (vx, vy)
                in  if rx < ry then
                      (x := Link { parent=y }; y := Root { rank=ry, value=v };
                       y)
                    else if rx > ry then
                      (y := Link { parent=x }; x := Root { rank=rx, value=v };
                       x)
                    else
                      (y := Link { parent=x };
                       x := Root { rank=rx + 1, value=v };
                       x)
                end
             | _ => raise Fail "impossible"
    end
end
