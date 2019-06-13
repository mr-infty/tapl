module Exercise_5_2_11

import Ch05.LambdaCalculusWithArith

%default total

-- The implementation below is the simple (and naive) one
||| Term representing a function that, given a list of Church numerals (encoded as in ex. 5.2.8),
||| will return their sum
listsum_naive : Term
listsum_naive = lambda 0
                       (\l => l . plus . church_zero)

-- The implementation below uses the fix-point combinator
||| Term representing a function that, given a list of Church numerals (encoded as in ex. 5.2.8),
||| will return their sum
listsum : Term
listsum = fix . g where
  g : Term
  g = lambda 0
             (\f => (lambda 1
                            (\l => IfThenElse (realbool . (isnil . l))
                                              church_zero
                                              (plus . (head . l) . (f . (tail . l))))))
