module Ch05.Exercise_5_2_5

import Ch05.LambdaCalculus

%default total

||| `sub m n` yields the result of subtracting `n` from `m` (Church numerals).
|||
||| More precisely, it yields the smallest church numeral `z` such that
|||
|||     m <= n+z
public export
sub : Term
sub = let m = Var 0
          n = Var 1 in
          Abs 0 (Abs 1 (n . prd) . m)
