module Ch05.Exercise_5_2_4

import Ch05.LambdaCalculus

%default total

||| `pow m n` is `m` raised to the power `n`
pow : Term
pow = Abs 0 (Abs 1 ((Var 1) . (times . (Var 0))) . church_one)

