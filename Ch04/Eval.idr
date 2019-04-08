module Ch04.Eval

import Ch03.Arith

%default total

mutual
  namespace IsBadBool
    ||| Propositional type describing that a term is a "bad boolean".
    data IsBadBool : Term -> Type where
      IsStuckTerm : {pf : IsStuck t} -> IsBadBool t
      IsNat : {pf : IsNumValue t} -> IsBadBool t

  namespace IsBadNat
    ||| Propositional type describing that a term is a "bad nat".
    data IsBadNat : Term -> Type where
      IsStuckTerm : {pf : IsStuck t} -> IsBadNat t
      IsBool : {pf : IsBoolValue t} -> IsBadNat t
  
  ||| Propositional type describing that a term is stuck.
  data IsStuck : Term -> Type where
    EIfWrong : {t1,t2,t3 : Term} ->
               {pf : IsBadBool t1} ->
               IsStuck (IfThenElse t1 t2 t3)
    ESuccWrong : {t : Term} ->
                 {pf : IsBadNat t} ->
                 IsStuck (Succ t)
    EPredwrong : {t : Term} ->
                 {pf : IsBadNat t} ->
                 IsStuck (Pred t)
    EIsZeroWrong : {t : Term} ->
                   {pf : IsBadNat t} ->
                   IsStuck (IsZero t)

-- We are using an ad hoc definition of what it means to be stuck,
-- which is not exactly the one used in the book (normal but not a value).
-- This is for convenience. (TODO: Fix this maybe.)
||| Propositional type describing that a term is fully evaluated.
FullyEvaluated : Term -> Type
FullyEvaluated t = Either (IsStuck t) (IsValue t)

||| Given a term, returns its value.
smallStep_eval : (t : Term) -> (v : Term ** (EvalsToStar t v, FullyEvaluated v))
smallStep_eval t = ?smallStep_eval_rhs
