fun f (b, x1, x2, y1, y2) =
  let fun mk () =
        if b then
          let fun g z = (x1, z, x2)
          in  g
          end
        else
          let fun h z = (y1, z, y2)
          in  h
          end
  in  mk
  end

