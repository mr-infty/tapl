module Ch05.Exercise_5_2_7

import Ch05.LambdaCalculus
import Ch05.Exercise_5_2_5

%default total

||| `le m n` tests whether `m` is less than or equal to `n`
le : Term
le = let m = Var 0
         n = Var 1 in
         Abs 0 (Abs 1 (iszro . (sub . m . n)))

||| Test whether two Church numerals are equal
equal : Term
equal = let m = Var 0
            n = Var 1
            m_le_n = le . m . n
            n_le_m = le . n . m in
            Abs 0 (Abs 1 (and . m_le_n . n_le_m))
