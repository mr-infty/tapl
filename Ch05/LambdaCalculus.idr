module Ch05.LambdaCalculus

import Ch03.Relations

%access public export

||| The type of variables
Variable : Type
Variable = Nat

||| The type of terms in the untyped lambda calculus
data Term = Var Variable
          | Abs Variable Term
          | App Term Term

||| Convenient infix notation for construction of function application terms
(.) : Term -> Term -> Term
(.) = App

-- TODO: Can we get rid of the argument `n`?
||| Convenience function for constructing lambda terms
lambda : Nat -> (Term -> Term) -> Term
lambda n f = Abs n (f (Var n))

MultiAppArgType : (numArgs : Nat) -> Type
MultiAppArgType Z = Term
MultiAppArgType (S k) = Term -> MultiAppArgType k

-- K_0 = id : a -> a
-- K : a -> b -> a
-- K_2 : a -> b -> b -> a
-- K_n : a -> b ... -> b -> a
--
-- K f t
-- K_2 f t1 t2 := K (K f t1) t2
--
-- K_{n+1} : a -> b -> .. -> b -> (b -> a)
-- K_{n+1} f x1 ... x{n+1} = K (K_n f x1 ... x_n) x_{n+1}

||| Convenience version of the `App` constructor that allows for a variable number of arguments.
multi_app : {numArgs : Nat} -> (MultiAppArgType numArgs -> Term)
multi_app {numArgs = Z} = \f => f
multi_app {numArgs = (S k)} = ?hole--(\f : Term => App f t) . (multi_app {numArgs=k})

data DirectSubterm : Term -> Term -> Type where
  IsAbsBody : {x : Variable} ->
              {t : Term} ->
              DirectSubterm t (Abs x t)
  IsAppFun : {f, x : Term} ->
             DirectSubterm f (App f x)

  IsAppArg : {f, x : Term} ->
             DirectSubterm x (App f x)


Subterm : Term -> Term -> Type
Subterm = ReflSymmClos DirectSubterm

-- vars (x) = {x}
-- vars (lambda x . t) = {x} \cup vars (t)
-- vars (f t) = vars(f) \cup vars(t)
-- 
-- bound_vars (x) = {}
-- bound_vars (lambda x . t) = \{x\} \cup bound_vars(t)
-- bound_vars (f t) = bound_vars(f) \cup bound_vars(t)
--
-- free_vars (x) = {}
-- free_vars (lambda x . t) = free_vars(t) - \{x\}
-- free_vars (f t) = free_vars(f) \cup free_vars(t)
-- 



namespace Occurs
  ||| Propositional type describing that a variable occurs in a term.
  data Occurs : Variable -> Term -> Type where
    IsVar : (x : Variable) ->
            Occurs x (Var x)

namespace OccursFree
  ||| Propositional type describing that a variable occurs freely in a term.
  data OccursFree : Variable -> Term -> Type where
    IsVar : (x : Variable) ->
            OccursFree x (Var x)
    InBody : {x,y : Variable} ->
             {t : Term} ->
             Not (x = y) ->
             OccursFree x t ->
             OccursFree x (Abs y t)
    InAppFun : {x : Variable} ->
               {f, t : Term} ->
               OccursFree x f ->
               OccursFree x (App f t)
    InAppArg : {x : Variable} ->
               {f, t : Term} ->
               OccursFree x t ->
               OccursFree x (App f t)

Closed : Term -> Type
Closed t = (x : Variable) -> Not (OccursFree x t)

namespace OccursBound
  ||| Propositional type describing that a variable occurs bound in a term.
  data OccursBound : Variable -> Term -> Type where


||| The identity combinator.
id : Term
id = Abs 0 (Var 0)

||| Proof that the identity combinator is closed.
id_is_closed : Closed Ch05.LambdaCalculus.id
id_is_closed x pf_occurs_free = case pf_occurs_free of
                                     (InBody pf_ne pf_in_t) => case pf_in_t of
                                                                    (IsVar Z) => pf_ne Refl

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
