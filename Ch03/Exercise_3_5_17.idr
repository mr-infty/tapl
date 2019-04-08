module Ch03.Exercise_3_5_17

import Ch03.Arith

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

lemma_EPred : {t1, t1' : Term} ->
              {pf : IsValue v} ->
              (x : EvalsTo t1 t1') ->
              (r' : BInE (Pred t1') v ** d' = from_BInE_to_E r') ->
              (r : BInE (Pred t1) v ** Cons (EPred x) d' = from_BInE_to_E r)
lemma_EPred {pf} x (r' ** pf') = case r' of
                                      BInEValue {pf=pf_val} => absurd (predNotValue pf_val)
                                      BInEPredZero y => (BInEPredZero (Cons x y) ** cong pf')
                                      BInEPredSucc {pf=pf_v} y => (BInEPredSucc {pf=pf_v} (Cons x y) ** cong pf')

lemma_EIsZero : {t1, t1', v : Term} ->
                {pf : IsValue v} ->
                (x : EvalsTo t1 t1') ->
                (r' : BInE (IsZero t1') v ** d' = from_BInE_to_E r') ->
                (r : BInE (IsZero t1) v ** Cons (EIsZero x) d' = from_BInE_to_E r)
lemma_EIsZero {pf} x (r' ** pf') = case r' of
                                        BInEValue {pf=pf_val} => absurd (isZeroNotValue pf_val)
                                        BInEIsZeroZero y => (BInEIsZeroZero (Cons x y) ** cong pf')
                                        BInEIsZeroSucc {pf=pf_v} y => (BInEIsZeroSucc {pf=pf_v} (Cons x y) ** cong pf')

||| Deconstructs a derivation of a term `t` to a value `v` in the `E`-calculus into a (one-step) derivation
||| in the `BInE`-calculus.
from_E_to_BInE : {pf : IsValue v} ->
                 (d : EvalsToStar t v) -> (r : BInE t v ** d = from_BInE_to_E r)
from_E_to_BInE {pf} {t = True} Refl = (BInEValue {pf=ConvertedFrom (Left True)} {v=True} ** Refl)
from_E_to_BInE {pf} {t = True} (Cons x y) = absurd (valuesDontEvaluate {pf=ConvertedFrom (Left True)} x)
from_E_to_BInE {pf} {t = False} Refl = (BInEValue {pf=ConvertedFrom (Left False)} {v=False} ** Refl)
from_E_to_BInE {pf} {t = False} (Cons x y) = absurd (valuesDontEvaluate {pf=ConvertedFrom (Left False)} x)
from_E_to_BInE {pf} {t = (IfThenElse x y z)} Refl = absurd (ifThenElseNotNormal pf)
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
                                                     EPredZero => case valuesAreNormal {pf=ConvertedFrom (Right Zero)} z of
                                                                       Refl => (BInEPredZero Refl ** Refl)
                                                     EPredSucc {nv1} {pf=pf_nv} => case valuesAreNormal {pf=numValueIsValue pf_nv} z of
                                                                                        Refl => (BInEPredSucc {pf=pf_nv} Refl ** Refl)
                                                     EPred y' => lemma_EPred {pf=pf} y' (from_E_to_BInE {pf=pf} z)
from_E_to_BInE {pf} {t = (IsZero x)} Refl = absurd (isZeroNotValue pf)
from_E_to_BInE {pf} {t = (IsZero x)} (Cons y z) = case y of
                                                       EIsZeroZero => case valuesAreNormal {pf=ConvertedFrom (Left True)} z of
                                                                           Refl => (BInEIsZeroZero Refl ** Refl)
                                                       EIsZeroSucc => case valuesAreNormal {pf=ConvertedFrom (Left False)} z of
                                                                           Refl => (BInEIsZeroSucc Refl ** Refl)
                                                       EIsZero y' => lemma_EIsZero {pf=pf} y' (from_E_to_BInE {pf=pf} z)

||| Converts a derivation in `BInE`-calculus to a derivation in the `B`-calculus.
from_BInE_to_B : {pf : IsValue v} -> BInE t v -> BigEvalsTo t v
from_BInE_to_B {pf} BInEValue = BValue {pf=pf}
from_BInE_to_B {pf} (BInEIfTrue y z) = let pf_true = ConvertedFrom (Left True)
                                           y' = fst (from_E_to_BInE {pf=pf_true} y)
                                           z' = fst (from_E_to_BInE {pf=pf} z) in
                                           BIfTrue {pf=pf} (from_BInE_to_B {pf=pf_true} y') (from_BInE_to_B {pf=pf} z')
from_BInE_to_B {pf} (BInEIfFalse y z) = let pf_false = ConvertedFrom (Left False)
                                            y' = fst (from_E_to_BInE {pf=pf_false} y)
                                            z' = fst (from_E_to_BInE {pf=pf} z) in
                                            BIfFalse {pf=pf} (from_BInE_to_B {pf=pf_false} y') (from_BInE_to_B {pf=pf} z')
from_BInE_to_B {pf} (BInESucc {pf=pf_nv} y) = let y' = fst (from_E_to_BInE {pf=numValueIsValue pf_nv} y) in
                                                  BSucc {pf=pf_nv} (from_BInE_to_B {pf=numValueIsValue pf_nv} y')
from_BInE_to_B {pf} (BInEPredZero x) = let pf_zero = ConvertedFrom (Right Zero)
                                           x' = fst (from_E_to_BInE {pf=pf_zero} x) in
                                           BPredZero (from_BInE_to_B {pf=pf_zero} x')
from_BInE_to_B {pf} (BInEPredSucc {pf=pf_v} y) = let pf_succ = numValueIsValue (succNumValueIsNumValue pf_v)
                                                     y' = fst (from_E_to_BInE {pf=pf_succ} y) in
                                                     BPredSucc {pf=pf_v} (from_BInE_to_B {pf=pf_succ} y')
from_BInE_to_B {pf} (BInEIsZeroZero x) = let pf_zero = ConvertedFrom (Right Zero)
                                             x' = fst (from_E_to_BInE {pf=pf_zero} x) in
                                             BIsZeroZero (from_BInE_to_B {pf=pf_zero} x')
from_BInE_to_B {pf} (BInEIsZeroSucc {pf=pf_v} y) = let pf_succ = numValueIsValue (succNumValueIsNumValue pf_v)
                                                       y' = fst (from_E_to_BInE {pf=pf_succ} y) in
                                                       BIsZeroSucc {pf=pf_v} (from_BInE_to_B {pf=pf_succ} y')

||| Proof that if a term `t` evaluates to a value `v` under the reflexive transitive
||| closure of the small-step evaluation rules, then it also evaluates to it under the
||| big-step evaluation rules.
starImpliesBig : {pf : IsValue v} -> EvalsToStar t v -> BigEvalsTo t v
starImpliesBig {pf} d = from_BInE_to_B {pf=pf} (fst (from_E_to_BInE {pf=pf} d))

||| Proof that if a term `t` evaluates to a value `v` under the big-step evaluation rules,
||| then it also evaluates to it under the reflexive transitive closure of the small-step
||| rules.
bigImpliesStar : {pf : IsValue v} -> BigEvalsTo t v -> EvalsToStar t v
bigImpliesStar {pf} BValue = Refl
bigImpliesStar {pf} (BIfTrue y z) = let y' = bigImpliesStar {pf=ConvertedFrom (Left True)} y
                                        z' = bigImpliesStar {pf=pf} z in
                                        from_BInE_to_E (BInEIfTrue {pf=pf} y' z')
bigImpliesStar {pf} (BIfFalse y z) = let y' = bigImpliesStar {pf=ConvertedFrom (Left False)} y
                                         z' = bigImpliesStar {pf=pf} z in
                                         from_BInE_to_E (BInEIfFalse {pf=pf} y' z')
bigImpliesStar {pf} (BSucc {pf=pf_nv} y) = let y' = bigImpliesStar {pf=numValueIsValue pf_nv} y in
                                               from_BInE_to_E (BInESucc {pf=pf_nv} y')
bigImpliesStar {pf} (BPredZero x) = let x' = bigImpliesStar {pf=pf} x in
                                        from_BInE_to_E (BInEPredZero x')
bigImpliesStar {pf} (BPredSucc {pf=pf_nv} y) = let y' = bigImpliesStar {pf=numValueIsValue (succNumValueIsNumValue pf_nv)} y in
                                                   from_BInE_to_E (BInEPredSucc {pf=pf_nv} y')
bigImpliesStar {pf} (BIsZeroZero x) = let x' = bigImpliesStar {pf=ConvertedFrom (Right Zero)} x in
                                          from_BInE_to_E (BInEIsZeroZero x')
bigImpliesStar {pf} (BIsZeroSucc {pf=pf_nv} y) = let y' = bigImpliesStar {pf=numValueIsValue (succNumValueIsNumValue pf_nv)} y in
                                                     from_BInE_to_E (BInEIsZeroSucc {pf=pf_nv} y')
