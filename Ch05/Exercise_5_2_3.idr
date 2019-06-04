module Ch05.Exercise_5_2_3

import Ch05.LambdaCalculus

%default total

||| Alternative (more concise) way to define multiplication of Church numerals
times' : Term
times' = Abs 0 (Abs 1 ((Var 0) . (Var 1)))
