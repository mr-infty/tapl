module Ch05.EvalLambdaCalculus

import Ch05.LambdaCalculus

%default total

-----------------------------------------------------------------------
-- Evaluating the "evil" lambda calculus, one parentheses at a time.
-----------------------------------------------------------------------

-- Remark: Defining the evaluation rules for the toy language of
-- arithmetic expressions was very straightforward (even though
-- implementing the evaluation function turned out to be quite
-- involved, since we needed to prove totality.)
-- 
-- However, for the lambda calculus it isn't because of the problem
-- of variable capture. The book only makes some vagues hand gestures
-- suggesting we work with "terms up to alpha-conversion" and then
-- proceeds to give a prescription of substitution that is only partially
-- defined on terms.
--
-- To give sense to this vague suggestion, we might be tempted to
-- introduce a parametrized type `AlphaConverts t1 t2` that
-- says when two terms can be derived from each other by alpha
-- conversion (renaming of bound variables). Of course, the operation
-- of alpha conversion is a special case of variable substitution so
-- it seems we get stuck in a vicious circle.
-- Supposing that we won't, we might then proceed to form something
-- like a quotient type by forcing the existence of a function
--
--     AlphaConverts t1 t2 -> (t1 = t2)
--
-- (e.g. using believe_me). But that would be serious messing with
-- the type checker, so I don't like it.
--
-- So, I think I proceed as follows:
-- Define substitution using mutual recursion between a partially defined
-- substitution operation and an alpha-conversion operation that converts any
-- term to a term accepted by the partially defined substitution function.

-- TODO: Fix the definition below.
data AlphaConverts : Term -> Term -> Type where
  RenameLambda : {x, y : Variable} ->
                 {t : Term} ->
                 Not (OccursFree x t) ->
                 Not (OccursFree y t) ->
                 AlphaConverts (Abs x t) (Abs y t)
  ConvertBody : AlphaConverts t t' ->
                AlphaConverts (Abs x t) (Abs x t')
  ConvertsFun : AlphaConverts f f' ->
                AlphaConverts (App f x) (App f' x)
  ConvertsArg : AlphaConverts x x' ->
                AlphaConverts (App f x) (App f x')
