module Ch05.Exercise_5_2_2

import Ch05.LambdaCalculus

%default total

||| Alternative version of the Church numeral successor
scc' : Term
scc' = Abs 0 (Abs 1 (Abs 2 (App (App (Var 0) (Var 1)) (App (Var 1) (Var 2)))))
