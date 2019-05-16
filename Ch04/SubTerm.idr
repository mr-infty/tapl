module Ch04.SubTerm

import Ch03.Arith

||| Propositional type describing that one term is an direct subterm of another one.
data DirectSubTerm : Term -> Term -> Type where
  IsIfTerm : (x : Term) -> DirectSubTerm x (IfThenElse x y z)
  IsThenTerm : (y : Term) -> DirectSubTerm y (IfThenElse x y z)
  IsElseTerm : (z : Term) -> DirectSubTerm z (IfThenElse x y z)
  IsSuccSubTerm : (x : Term) -> DirectSubTerm x (Succ x)
  IsPredSubTerm : (x : Term) -> DirectSubTerm x (Pred x)

||| Propositional type describing that one term is a subterm of another one.
data SubTerm : Term -> Term -> Type where
  IsSubTermOfDirectSubTerm : SubTerm x y -> DirectSubTerm y z -> SubTerm x z
  IsEqual : SubTerm x x
