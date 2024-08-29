fun apply f x = f x;

fun length [] = 0
  | length (x :: xs) = 1 + apply length xs
