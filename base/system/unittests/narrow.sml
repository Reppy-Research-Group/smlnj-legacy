fun f (a, b, c, d, e) =
  let fun g h = if h = 0 then a else (print "hello"; g (a + b + c + d + e + h))
  in  g 10
  end
