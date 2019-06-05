module Ch05.Exercise_5_2_8

import Ch05.LambdaCalculus

%default total

-- Lists are represented by their corresponding fold function. That is, a list
-- [x, y, z] is identified with the function
--
--    f |-> ( c |-> f x (f y (f z c))) )
-- 
-- Where f is any 2-ary function (since the untyped lambda calculus is untyped, of
-- course we can't talk about arities).

||| The term representing the empty list
nil : Term
nil = Abs 0 (Abs 1 (Var 1))--?nil_rhs

||| The term representing the cons combinator
cons : Term
cons = let car = Var 0 -- not to be confused with the car combinator below
           cdr = Var 1 -- --------------------------- cdr ----------------
           f = Var 2
           c = Var 3 in
           Abs 0 (Abs 1 (Abs 2 (Abs 3 (f . car . (cdr . f . c)))))

||| Checks whether a list is nil
isnil : Term
isnil = let l = Var 0
            f = Abs 1 (Abs 2 fls) in
            Abs 0 (l . f . tru)

||| The term representing the "car" combinator
head : Term
head = let l = Var 0 in
           Abs 0 l . fst . nil

||| The term representing the "cdr" combinator
tail : Term
tail = let l = Var 0
           x = Var 1
           y = Var 2
           f = Abs 1 (Abs 2 pair . (snd . y) . (cons . x . (snd . y)))
           c = pair . nil . nil in
           Abs 0 (fst . (l . f . c))
