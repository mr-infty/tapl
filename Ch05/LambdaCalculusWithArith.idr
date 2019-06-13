module Ch05.LambdaCalculusWithArith

import Ch03.Relations

%default total
%access public export

--------------------------------------------------------------------------------
-- The lambda calculus extended by native arithmetic expressions.
--------------------------------------------------------------------------------
--
-- Remark: It kinda sucks to have to repeat the definitions of the lambda
-- calculus and the language of arithmetic expressions. In particular because
-- in the book Pierce doesn't even bother to write down the language and simply
-- waves his hands. So you expect to be able to just formally combine the two
-- languages.
-- However, I don't know a convenient way to do that since Idris has no subtyping.
-- It would be possible to define something like
--
-- data Term = Lambda Ch05.LambdaCalculus.Term
--           | Arith Ch03.Arith.Term
--
-- but that would be kinda awkward.
--
-- TL;DR: I'm just gonna repeat definitions as that seems simpler.
--------------------------------------------------------------------------------

||| The type of variables
Variable : Type
Variable = Nat

-- Pierce doesn't bother to actually define this calculus (neither in the book
-- nor the software available at https://www.cis.upenn.edu/~bcpierce/tapl).
-- So I'm using the simplest, most naive definition I can imagine here.
||| Terms in the lambda calculus extended by arithmetic expressions.
data Term = True
          | False
          | IfThenElse Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Var Variable
          | Abs Variable Term
          | App Term Term

||| Convenient infix notation for construction of function application terms
(.) : Term -> Term -> Term
(.) = App

-- TODO: Can we get rid of the argument `n`?
||| Convenience function for constructing lambda terms
lambda : Nat -> (Term -> Term) -> Term
lambda n f = Abs n (f (Var n))


-----------------------------------------------------------------------
-- The stuff below is literally copy pasted from Ch05.LambdaCalculus

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------

||| The Church boolean true
tru : Term
tru = Abs 1 (Abs 0 (Var 1))

||| The Church boolean false
fls : Term
fls = Abs 1 (Abs 0 (Var 0))

||| Church encoding of the if-then-else operator
test : Term
test = Abs 2 (Abs 1 (Abs 0 (App (App (Var 2) (Var 1)) (Var 0))))

||| Logical AND operator for Church booleans.
and : Term
and = Abs 0 (Abs 1 (App (App (Var 0) (Var 1)) fls))

--------------------------------------------------------------------------------
-- Pairs
--------------------------------------------------------------------------------

||| Church pair constructor
pair : Term
pair = Abs 0 (Abs 1 (Abs 2 (App (App (Var 2) (Var 0)) (Var 1))))

||| Projection onto the first component of a pair
fst : Term
fst = Abs 0 (Abs 1 (Var 0))

||| Projection onto the second component of a pair
snd : Term
snd = Abs 0 (Abs 1 (Var 1))

--------------------------------------------------------------------------------
-- Numerals
--------------------------------------------------------------------------------

||| The Church numeral zero.
church_zero : Term
church_zero = Abs 1 (Abs 0 (Var 0))

||| The Church numeral one.
church_one : Term
church_one = Abs 1 (Abs 0 (App (Var 1) (Var 0)))

||| The Church numeral two.
church_two : Term
church_two = Abs 1 (Abs 0 (App (Var 1) (App (Var 1) (Var 0))))

||| The successors function for Church numerals
scc : Term
scc = Abs 0 (Abs 1 (Abs 2 (App (Var 1) (App (App (Var 0) (Var 1)) (Var 2)))))

||| Addition of Church numerals
plus : Term
plus = Abs 0 (Abs 1 (Abs 2 (Abs 3 ((Var 0) . (Var 2)) . (((Var 1) . (Var 2)) . (Var 3)))))

||| Multiplication of Church numerals
times : Term
times = Abs 0 (Abs 1 ((Var 0) . (plus . (Var 1))) . church_zero)

||| Tests whether a Church numeral is zero or not
iszro : Term
iszro = Abs 0 ((Var 0) . (Abs 0 fls)) . tru

||| The predecessor function on Church numerals
prd : Term
prd = let zz = pair . church_zero . church_zero
          ss = Abs 0 (pair . (snd . (Var 0)) . (scc . (snd . (Var 0)))) in
          Abs 0 (fst . ((Var 0) . ss) . zz)

--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

-- See Ch05.Exercise_5_2_8

--------------------------------------------------------------------------------
-- Self-replicating terms
--------------------------------------------------------------------------------

||| The (?) simplest self-replicating term in the lambda calculus
omega : Term
omega = let x = Var 0
            f = Abs 0 (x . x) in
            f . f

||| The call-by-value version of the fix-point combinator (i.e. Y combinator)
fix : Term
fix = let f = Var 0
          x = Var 1
          y = Var 2
          t = Abs 1 f . (Abs 2 (x . x . y)) in
          Abs 0 (t . t)


-----------------------------------------------------------------------
-- Copy pasted exercises

||| `sub m n` yields the result of subtracting `n` from `m` (Church numerals).
|||
||| More precisely, it yields the smallest church numeral `z` such that
|||
|||     m <= n+z
sub : Term
sub = let m = Var 0
          n = Var 1 in
          Abs 0 (Abs 1 (n . prd) . m)

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

-----------------------------------------------------------------------
-- Stuff below is lifted wholesale from exercise 5.2.8

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

-----------------------------------------------------------------------
-- Stuff below is not copy pasted.

||| Term representing a function converting Church booleans into "real" booleans.
realbool : Term
realbool = lambda 0
                  (\b => b . True . False)

||| Term representing a function converting "real" booleans to Church booleans.
churchbool : Term
churchbool = lambda 0
                    (\b => IfThenElse b tru fls)

||| Term representing a function of two arguments returning a "real" boolean
||| specifying whether they are equal or not, at least if both arguments provided
||| are Church numerals.
realeq : Term
realeq = lambda 0
                (\m => lambda 1
                              (\n => (equal . m . n) . True . False))

||| Term representing a function converting a Church numeral into a primitive natural number
realnat : Term
realnat = lambda 0
                 (\n => n . (lambda 1 (\x => Succ x)) . church_zero) -- TODO: Rename church_zero to c0 etc.
