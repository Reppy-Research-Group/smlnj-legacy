structure A : sig val result : (unit -> (unit -> int) * int) list end = struct
  val N = 10

  (* val x: (unit -> int list) ref = ref (fn () => []) *)
  (* fun blackhole v = (x := v; x := (fn () => [])) *)

  fun f (v, w, x, y, z) =
    let fun g () =
          let val u = hd v
              (* fun getV () = v *)
              fun h () =
                let fun i () = w + x + y + z + 3
                in  (i, u)
                end
          in  (* blackhole getV; *) h
          end
    in  g
    end

  fun big n = if n < 1 then [0] else n :: big (n - 1)

  fun loop (n, res) =
    if n < 1 then res
    else (let val s = f (big N, 0, 0, 0, 0) ()
          in  loop (n - 1, s :: res)
          end)

  val result = loop (N, [])
end
