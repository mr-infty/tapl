module Arith

%default total

----------------------------
-- Term syntax
----------------------------

namespace Terms
  data Term = True
            | False
            | IfThenElse Term Term Term
            | Zero
            | Succ Term
            | Pred Term
            | IsZero Term

namespace Values
  mutual
    Value : Type
    Value = Either BoolValue NumValue

    data BoolValue = True | False
    data NumValue = Zero | Succ NumValue

||| Converts a boolean value to its corresponding term
bv2t : BoolValue -> Term
bv2t True = True
bv2t False = False

||| Converts a numeric value to its corresponding term
nv2t : NumValue -> Term
nv2t Zero = Zero
nv2t (Succ x) = Succ (nv2t x)

||| Converts a value to its corresponding term
v2t : Value -> Term
v2t (Left bv) = bv2t bv
v2t (Right nv) = nv2t nv

namespace IsValue
  ||| Propositional type describing that a term "is" indeed a value
  data IsValue : Term -> Type where
    ConvertedFrom : (v : Value) -> IsValue (v2t nv)

namespace IsNumValue
  ||| Propositional type describing that a term "is" indeed a numeric value
  data IsNumValue : Term -> Type where
    ConvertedFrom : (nv : NumValue) -> IsNumValue (v2t (Right nv))

----------------------------
-- Evaluation rules
----------------------------

||| Propositional type describing that the first term one-step-evaluates to the second
|||
||| Explicitly, an inhabitant of `EvalsTo t1 t2` is a proof that `t1` evaluates to `t2` in one step.
data EvalsTo : Term -> Term -> Type where
  ESucc : EvalsTo t1 t2 -> EvalsTo (Succ t1) (Succ t2)
  EPredZero : EvalsTo (Pred Zero) Zero
  EPredSucc : {pf : IsNumValue nv1} -> EvalsTo (Pred (Succ nv1)) nv1
  EPred : EvalsTo t1 t1 -> EvalsTo (Pred t1) (Pred t2)
  EIsZeroZero : EvalsTo (IsZero Zero) Zero
  EIsZeroSucc : {pf : IsNumValue nv1} -> EvalsTo (IsZero (Succ nv1)) False
  EIsZero : EvalsTo t1 t2 -> EvalsTo (IsZero t1) (IsZero t2)

namespace ReflSymmClos
  ||| Type representing the reflexive transitive closure of a relation
  |||
  ||| Given a relational type `rel : ty -> ty -> Type`, `ReflSymmClos rel` is its reflexive and
  ||| transitive closure.
  data ReflSymmClos : (rel : ty -> ty -> Type) -> ty -> ty -> Type where
    Refl : ReflSymmClos rel x x
    --Snoc : ReflSymmClos rel t t' -> (rel t' t'') -> ReflSymmClos rel t t''
    Cons : (rel t t') -> ReflSymmClos rel t' t'' -> ReflSymmClos rel t t''

||| Propositional type describing that the first term evaluates to the second in a finite number of steps
|||
||| Explicitly, an inhabitant of `EvalToStar t1 t2` is a proof that there is a finite sequence
||| 
|||     t1 = s_0, s_1, ..., s_n = t2
|||
||| of terms (where `0 <= n`), such that `s_i` one-step-evaluates to `s_{i+1}`.
EvalsToStar : Term -> Term -> Type
EvalsToStar = ReflSymmClos EvalsTo

----------------------------
-- Big Step Evaluation rules
----------------------------

||| Propositional type describing that the first term big-step evaluates to the second
data BigEvalsTo : Term -> Term -> Type where
  BValue : {pf : IsValue v} -> BigEvalsTo v v
  BIfTrue : {pf : IsValue v2} ->
            BigEvalsTo t1 true ->
            BigEvalsTo t2 v2 -> 
            BigEvalsTo (IfThenElse t1 t2 t3) v2
  BIfFalse : {pf : IsValue v3} ->
             BigEvalsTo t1 false ->
             BigEvalsTo t3 v3 -> 
             BigEvalsTo (IfThenElse t1 t2 t3) v3
  BSucc : {pf : IsNumValue nv1} ->
          BigEvalsTo t1 nv1 -> 
          BigEvalsTo (Succ t1) (Succ nv1)
  BPredZero : BigEvalsTo t1 Zero ->
              BigEvalsTo (Pred t1) Zero
  BPredSucc : {pf : IsNumValue nv1} ->
              BigEvalsTo t1 (Succ nv1) ->
              BigEvalsTo (Pred t1) nv1
  BIsZeroZero : BigEvalsTo t1 Zero ->
                BigEvalsTo (IsZero t1) True
  BIsZeroSucc : {pf : IsNumValue nv1} ->
                BigEvalsTo t1 (Succ nv1) ->
                BigEvalsTo (IsZero t1) False


----------------------------
-- Exercise 3.5.17
----------------------------
-- TODO: Move this into extra file!

lemma1 : {pf : IsValue v} -> EvalsTo t1 t2 -> BigEvalsTo t2 v -> BigEvalsTo t1 v
lemma1 {pf} (ESucc x) y = ?lemma1_rhs_1
lemma1 {pf} EPredZero y = ?lemma1_rhs_2
lemma1 {pf} EPredSucc y = ?lemma1_rhs_3
lemma1 {pf} (EPred x) y = ?lemma1_rhs_4
lemma1 {pf} EIsZeroZero y = ?lemma1_rhs_5
lemma1 {pf} EIsZeroSucc y = ?lemma1_rhs_6
lemma1 {pf} (EIsZero x) y = ?lemma1_rhs_7

starImpliesBig_ind_step : (pf : IsValue v) -> (x : EvalsTo t t') -> (y : BigEvalsTo t' v) -> BigEvalsTo t v
starImpliesBig_ind_step pf (ESucc x) y = ?starImpliesBig_ind_step_rhs_1
starImpliesBig_ind_step pf EPredZero y = ?starImpliesBig_ind_step_rhs_2
starImpliesBig_ind_step pf EPredSucc y = ?starImpliesBig_ind_step_rhs_3
starImpliesBig_ind_step pf (EPred x) y = ?starImpliesBig_ind_step_rhs_4
starImpliesBig_ind_step pf EIsZeroZero y = ?starImpliesBig_ind_step_rhs_5
starImpliesBig_ind_step pf EIsZeroSucc y = ?starImpliesBig_ind_step_rhs_6
starImpliesBig_ind_step pf (EIsZero x) y = ?starImpliesBig_ind_step_rhs_7

starImpliesBig : {pf : IsValue v} -> EvalsToStar t v -> BigEvalsTo t v
starImpliesBig {pf} Refl = BValue {pf=pf}
starImpliesBig {pf} (Cons x y) = starImpliesBig_ind_step pf x (starImpliesBig {pf=pf} y)

bigImpliesStar : {pf : IsValue v} -> BigEvalsTo t v -> EvalsToStar t v

----------------------------
-- Miscellanea
----------------------------

t1 : Term
t1 = IfThenElse False Zero (Succ Zero)

t2 : Term
t2 = IsZero (Pred (Succ Zero))

toString : Term -> String
toString True = "true"
toString False = "false"
toString (IfThenElse x y z) = "if " ++ toString x ++
                              " then " ++ toString y ++
                              " else " ++ toString z
toString Zero = "0"
toString (Succ x) = "succ (" ++ toString x ++ ")"
toString (Pred x) = "pred (" ++ toString x ++ ")"
toString (IsZero x) = "iszero (" ++ toString x ++ ")"

eval : Term -> Value
eval True = Left True
eval False = Left True
eval (IfThenElse x y z) = case eval x of
                               (Left r) => case r of
                                                True => eval y
                                                False => eval z
                               (Right l) => ?eval_rhs_1
eval Zero = Right Zero
eval (Succ x) = case eval x of
                     Left l => ?eval_rhs_4
                     Right r => Right (Succ r)
eval (Pred x) = case eval x of
                     Left l => ?eval_rhs_5
                     Right r => case r of
                                     Zero => Right Zero
                                     Succ x => Right x
eval (IsZero x) = case x of
                       Zero => Left True
                       Succ y => Left False
                       _ => ?eval_rhs2
  
size : Term -> Nat
size True = 1 
size False = 1
size (IfThenElse x y z) = (size x) + (size y) + (size z) + 1
size Zero = 1
size (Succ x) = S (size x)
size (Pred x) = S (size x)
size (IsZero x) = S (size x)

depth : Term -> Nat
depth True = 1
depth False = 1
depth (IfThenElse x y z) = (max (depth x) (max (depth y) (depth z))) + 1
depth Zero = 1
depth (Succ x) = S (depth x)
depth (Pred x) = S (depth x)
depth (IsZero x) = S (depth x)
