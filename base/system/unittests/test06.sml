fun iter (x, p, f) =
  let fun h (a, r) = if p (a, r) then a else h (f a, a)
  in  h (x, 1.0)
	end
