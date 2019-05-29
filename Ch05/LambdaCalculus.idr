module Ch05.LambdaCalculus

import Ch03.Relations

||| The type of variables
Variable : Type
Variable = Nat

||| The type of terms in the untyped lambda calculus
data Term = Var Variable
          | Abs Variable Term
          | App Term Term

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

||| The Church numeral zero.
church_zero : Term
church_zero = Abs 1 (Abs 0 (Var 0))

||| The Church numeral one.
church_one : Term
church_one = Abs 1 (Abs 0 (App (Var 1) (Var 0)))

||| The Church numeral two.
church_two : Term
church_two = Abs 1 (Abs 0 (App (Var 1) (App (Var 1) (Var 0))))

||| The Church boolean true
tru : Term
tru = Abs 1 (Abs 0 (Var 1))

||| The Church boolean false
fls : Term
fls = Abs 1 (Abs 0 (Var 0))

||| Church encoding of the if-then-else operator
test : Term
test = Abs 2 (Abs 1 (Abs 0 (App (App (Var 2) (Var 1)) (Var 0))))
