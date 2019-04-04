module Exercise_3_5_17

import Arith

%default total

--------------------------------------------------------------------------------
-- Exercise 3.5.17
--------------------------------------------------------------------------------

||| Big step evaluation rules expressed in terms of reflexive-transitive closure
||| of small-step evaluation rules
data BInE : Term -> Term -> Type where
  BInEValue : {pf : IsValue v} -> BInE v v
  BInEIfTrue : {pf : IsValue v2} ->
               {t1, t2, t3 : Term} ->
               EvalsToStar t1 True ->
               EvalsToStar t2 v2 ->
               BInE (IfThenElse t1 t2 t3) v2
  BInEIfFalse : {pf : IsValue v3} ->
                {t1, t2, t3 : Term} ->
                EvalsToStar t1 False ->
                EvalsToStar t3 v3 ->
                BInE (IfThenElse t1 t2 t3) v3
  BInESucc : {pf : IsNumValue nv1} ->
             {t1 : Term} ->
             EvalsToStar t1 nv1 ->
             BInE (Succ t1) (Succ nv1)
  BInEPredZero : {t1 : Term} ->
                 EvalsToStar t1 Zero ->
                 BInE (Pred t1) Zero
  BInEPredSucc : {t1 : Term} ->
                 {pf : IsNumValue nv1} ->
                 EvalsToStar t1 (Succ nv1) ->
                 BInE (Pred t1) nv1
  BInEIsZeroZero : {t1 : Term} ->
                   EvalsToStar t1 Zero ->
                   BInE (IsZero t1) True
  BInEIsZeroSucc : {t1 : Term} ->
                   {pf : IsNumValue nv1} ->
                   EvalsToStar t1 (Succ nv1) ->
                   BInE (IsZero t1) False

||| Given a (one-step) derivation in the `BInE`-calculus, computes its corresponding derivation
||| in the `E`-calculus.
from_BInE_to_E : BInE t v -> EvalsToStar t v
from_BInE_to_E BInEValue = Refl
from_BInE_to_E (BInEIfTrue {t2} {t3} x y) = map {func=(\t => IfThenElse t t2 t3)} EIf x
                                            ++ Cons EIfTrue y
from_BInE_to_E (BInEIfFalse {t2} {t3} x y) = map {func=(\t => IfThenElse t t2 t3)} EIf x
                                            ++ Cons EIfFalse y
from_BInE_to_E (BInESucc x) = map ESucc x
from_BInE_to_E (BInEPredZero x) = map EPred x ++ weaken EPredZero
from_BInE_to_E (BInEPredSucc {pf} x) = map EPred x ++ weaken (EPredSucc {pf=pf})
from_BInE_to_E (BInEIsZeroZero x) = map EIsZero x ++ weaken EIsZeroZero
from_BInE_to_E (BInEIsZeroSucc {pf} x) = map EIsZero x ++ weaken (EIsZeroSucc {pf=pf})

--------------------------------------------------------------------------------
-- Sublemmas of `from_E_to_BInE`
--------------------------------------------------------------------------------

lemma_EIfTrue : {t2, t3 : Term} ->
                {pf : IsValue v} ->
                (d' : EvalsToStar t2 v) ->
                (r : BInE (IfThenElse True t2 t3) v ** Cons EIfTrue d' = from_BInE_to_E r)
lemma_EIfTrue {pf} d' = (BInEIfTrue {pf=pf} Refl d' ** Refl)

lemma_EIfFalse : {t2, t3 : Term} ->
                 {pf : IsValue v} ->
                 (d' : EvalsToStar t3 v) ->
                 (r : BInE (IfThenElse False t2 t3) v ** Cons EIfFalse d' = from_BInE_to_E r)
lemma_EIfFalse {pf} d' = (BInEIfFalse {pf=pf} Refl d' ** Refl)

lemma_EIf : {t1, t2, t3 : Term} ->
            {pf : IsValue v} ->
            {x : EvalsTo t1 t1'} ->
            (d' : EvalsToStar (IfThenElse t1' t2 t3) v) ->
            (r' : BInE (IfThenElse t1' t2 t3) v ** d' = from_BInE_to_E r') ->
            (r : BInE (IfThenElse t1 t2 t3) v ** Cons (EIf x) d' = from_BInE_to_E r)
lemma_EIf {pf} {x} d' (r' ** pf') = case r' of
                                         BInEValue {pf} => absurd (ifThenElseNotNormal pf)
                                         BInEIfTrue d1 d2 => (BInEIfTrue {pf=pf} (Cons x d1) d2 ** cong pf')
                                         BInEIfFalse d1 d2 => (BInEIfFalse {pf=pf} (Cons x d1) d2 ** cong pf')

lemma_ESucc : {t1 : Term} ->
              {pf : IsValue v} ->
              (x : EvalsTo t1 t1') ->
              (r' : BInE (Succ t1') v ** d' = from_BInE_to_E r') ->
              (r : BInE (Succ t1) v ** Cons (ESucc x) d' = from_BInE_to_E r)
lemma_ESucc {pf} x (r' ** pf') = case r' of
                                      BInEValue => case succIsValueIf pf of
                                                        nv_pf@(ConvertedFrom nv) => (BInESucc {pf=nv_pf} (weaken x) ** cong pf')
                                      BInESucc {pf} d'' => (BInESucc {pf=pf} (Cons x d'') ** cong pf')

||| Deconstructs a derivation of a term `t` to a value `v` in the `E`-calculus into a (one-step) derivation
||| in the `BInE`-calculus.
from_E_to_BInE : {pf : IsValue v} ->
                 (d : EvalsToStar t v) -> (r : BInE t v ** d = from_BInE_to_E r)
from_E_to_BInE {pf} {t = True} Refl = (BInEValue {pf=ConvertedFrom (Left True)} {v=True} ** Refl)
from_E_to_BInE {pf} {t = True} (Cons x y) with (valuesDontEvaluate {pf=ConvertedFrom (Left True)} x)
  from_E_to_BInE {pf} {t = True} (Cons x y) | with_pat impossible
from_E_to_BInE {pf} {t = False} Refl = (BInEValue {pf=ConvertedFrom (Left False)} {v=False} ** Refl)
from_E_to_BInE {pf} {t = False} (Cons x y) with (valuesDontEvaluate {pf=ConvertedFrom (Left False)} x)
  from_E_to_BInE {pf} {t = False} (Cons x y) | with_pat impossible
from_E_to_BInE {pf} {t = (IfThenElse x y z)} Refl with (ifThenElseNotNormal pf)
  from_E_to_BInE {pf} {t = (IfThenElse x y z)} Refl | with_pat impossible
from_E_to_BInE {pf} {t = (IfThenElse x y z)} (Cons w s) = case w of
                                                               EIfTrue => lemma_EIfTrue {pf=pf} s
                                                               EIfFalse => lemma_EIfFalse {pf=pf} s
                                                               (EIf r) => lemma_EIf {pf=pf} s (from_E_to_BInE {pf=pf} s)
from_E_to_BInE {pf} {t = Zero} d = case valuesAreNormal' {pf=ConvertedFrom (Right Zero)} d of
                                        Refl => case d of
                                                     Refl => (BInEValue {pf=ConvertedFrom (Right Zero)} ** Refl)
                                                     (Cons x y) => absurd (valuesDontEvaluate {pf=ConvertedFrom (Right Zero)} x)
from_E_to_BInE {pf} {t = (Succ x)} Refl = case succIsValueIf pf of
                                               ConvertedFrom nv => (BInEValue {pf=ConvertedFrom (Right (Succ nv))} ** Refl)
from_E_to_BInE {pf} {t = (Succ x)} (Cons y z) = case y of
                                                     ESucc y' => lemma_ESucc {pf=pf} y' (from_E_to_BInE {pf=pf} z)
from_E_to_BInE {pf} {t = (Pred x)} Refl = absurd (predNotValue pf)
from_E_to_BInE {pf} {t = (Pred x)} (Cons y z) = case y of
                                                     EPredZero => ?from_E_to_BInE_rhs_1
                                                     EPredSucc => ?from_E_to_BInE_rhs_3
                                                     EPred y' => ?from_E_to_BInE_rhs_4
from_E_to_BInE {pf} {t = (IsZero x)} d = ?from_E_to_BInE_rhs_8

||| Proof that if a term `t` evaluates to a value `v` under the reflexive transitive
||| closure of the small-step evaluation rules, then it also evaluates to it under the
||| big-step evaluation rules.
starImpliesBig : {pf : IsValue v} -> EvalsToStar t v -> BigEvalsTo t v

||| Proof that if a term `t` evaluates to a value `v` under the big-step evaluation rules,
||| then it also evaluates to it under the reflexive transitive closure of the small-step
||| rules.
bigImpliesStar : {pf : IsValue v} -> BigEvalsTo t v -> EvalsToStar t v
