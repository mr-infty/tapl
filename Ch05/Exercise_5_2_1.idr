module Ch05.Exercise_5_2_1

import Ch05.LambdaCalculus

%default total

or : Term
or = Abs 0 (Abs 1 (App (App (Var 0) tru) (Var 1)))

not : Term
not = Abs 0 (Abs 1 (Abs 2 (App (App (Var 0) (Var 2)) (Var 1))))

