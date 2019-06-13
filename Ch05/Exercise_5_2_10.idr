module Exercise_5_2_10

import Ch05.LambdaCalculusWithArith

%default total

||| Terms representing a function converting primitive natural numbers
||| into Church numerals.
churchnat : Term
churchnat = fix . g where
  g : Term
  g = lambda 0
             (\f => lambda 1
                           (\n => IfThenElse (IsZero n)
                                             church_zero
                                             (scc . (f . (Pred n)))))
