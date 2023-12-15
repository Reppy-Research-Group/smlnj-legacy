fun funcA 0 = 0
  | funcA n = n + funcB (n - 1)
and funcB 0 = 1
  | funcB n = n * funcC (n - 1)
and funcC 0 = 2
  | funcC n = n - funcA (n - 1);

