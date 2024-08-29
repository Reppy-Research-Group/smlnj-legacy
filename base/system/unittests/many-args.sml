fun f (op+) z = 
  let
    fun fe 0 = 1
      | fe n = n - ma (fe (n - 1))
    and ma 0 = 0
      | ma n = n - fe (ma (n - 1))
    val (a, b, c, d, e, f, g, h, i, j, k, l, m, n, p, q, r, s, t, u, v, w, x, y)
       = if z then
      (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
       21, 22, 23, fe 30)
    else 
      (7, 8, 14, 15, 16, 17, fe 15, 9, 10, 11, 12, 13, 18, 19, 20, 1, 2, 3, 4, 5, 6,
       21, 22, 23)
  in a + b + c + d + e + f + g + h + i + j + k + l + m + n + p + q + r + s
  + t + u + v + w + x + y
  end
