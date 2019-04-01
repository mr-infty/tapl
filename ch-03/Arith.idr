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
    ConvertedFrom : (v : Value) -> IsValue (v2t v)

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
  EIfTrue : EvalsTo (IfThenElse True t2 t3) t2
  EIfFalse : EvalsTo (IfThenElse False t2 t3) t3
  EIf : EvalsTo t1 t1' -> EvalsTo (IfThenElse t1 t2 t3) (IfThenElse t1' t2 t3)
  ESucc : EvalsTo t1 t2 -> EvalsTo (Succ t1) (Succ t2)
  EPredZero : EvalsTo (Pred Zero) Zero
  EPredSucc : {pf : IsNumValue nv1} -> EvalsTo (Pred (Succ nv1)) nv1
  EPred : EvalsTo t1 t2 -> EvalsTo (Pred t1) (Pred t2)
  EIsZeroZero : EvalsTo (IsZero Zero) True
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
 
  ||| Appends two (appendable) elements of the reflexive-transitive closure of `rel` together,
  ||| thus realizing the transitivity of said closure
  (++) : ReflSymmClos rel t t' ->
         ReflSymmClos rel t' t'' ->
         ReflSymmClos rel t t''
  (++) Refl y = y
  (++) (Cons x z) y = Cons x (z ++ y)

  ||| Given `rel t1 t2`, returns the associated relation in the reflexive transitive closure,
  ||| thus realizing the "closure part" of said closure
  weaken : rel t1 t2 -> ReflSymmClos rel t1 t2
  weaken x = Cons x Refl

  ||| Given a function `f` defined on relations of type `rel`, applies that to a relation in the
  ||| reflexive-transitive closure of `rel`
  map : {func : ty -> ty} -> (f : {t1 : ty} -> {t2 : ty} -> rel t1 t2 -> rel (func t1) (func t2)) ->
        (ReflSymmClos rel t1 t2) ->
        (ReflSymmClos rel (func t1) (func t2))
  map {func} f Refl = Refl
  map {func} f (Cons x y) = Cons (f x) (map f y)

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
            BigEvalsTo t1 True ->
            BigEvalsTo t2 v2 -> 
            BigEvalsTo (IfThenElse t1 t2 t3) v2
  BIfFalse : {pf : IsValue v3} ->
             BigEvalsTo t1 False ->
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

--------------------------------------------------------------------------------
-- Exercise 3.5.17
--------------------------------------------------------------------------------
-- TODO: Move this into extra file!

||| Big step evaluation rules expressed in terms of reflexive-transitive closure
||| of small-step evaluation rules
data BInE : Term -> Term -> Type where
  BInEValue : {pf : IsValue v} -> BInE v v
  BInEIfTrue : {pf : IsValue v2} ->
               EvalsToStar t1 True ->
               EvalsToStar t2 v2 ->
               BInE (IfThenElse t1 t2 t3) v2
  BInEIfFalse : {pf : IsValue v3} ->
                EvalsToStar t1 False ->
                EvalsToStar t3 v3 ->
                BInE (IfThenElse t1 t2 t3) v3
  BInESucc : {pf : IsNumValue nv1} ->
             EvalsToStar t1 nv1 ->
             BInE (Succ t1) (Succ nv1)
  BInEPredZero : EvalsToStar t1 Zero ->
                 BInE (Pred t1) Zero
  BInEPredSucc : {pf : IsNumValue nv1} ->
                 EvalsToStar t1 (Succ nv1) ->
                 BInE (Pred t1) nv1
  BInEIsZeroZero : EvalsToStar t1 Zero ->
                   BInE (IsZero t1) True
  BInEIsZeroSucc : {pf : IsNumValue nv1} ->
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
-- Auxillary lemmas about evaluation and values
--------------------------------------------------------------------------------

||| Proof that values don't evaluate to anything in the `E`-calculus.
valuesDontEvaluate : {pf : IsValue v} -> EvalsTo v t -> Void
valuesDontEvaluate {pf = (ConvertedFrom (Left bv))} {v = (bv2t bv)} x = case bv of
                                                                             True => (case x of
                                                                                           EIfTrue impossible
                                                                                           EIfFalse impossible
                                                                                           (EIf _) impossible
                                                                                           (ESucc _) impossible
                                                                                           EPredZero impossible
                                                                                           EPredSucc impossible
                                                                                           (EPred _) impossible
                                                                                           EIsZeroZero impossible
                                                                                           EIsZeroSucc impossible
                                                                                           (EIsZero _) impossible)
                                                                             False => (case x of
                                                                                            EIfTrue impossible
                                                                                            EIfFalse impossible
                                                                                            (EIf _) impossible
                                                                                            (ESucc _) impossible
                                                                                            EPredZero impossible
                                                                                            EPredSucc impossible
                                                                                            (EPred _) impossible
                                                                                            EIsZeroZero impossible
                                                                                            EIsZeroSucc impossible
                                                                                            (EIsZero _) impossible)
valuesDontEvaluate {pf = (ConvertedFrom (Right nv))} {v = (nv2t nv)} x = case nv of
                                                                              Zero => (case x of
                                                                                            EIfTrue impossible
                                                                                            EIfFalse impossible
                                                                                            (EIf _) impossible
                                                                                            (ESucc _) impossible
                                                                                            EPredZero impossible
                                                                                            EPredSucc impossible
                                                                                            (EPred _) impossible
                                                                                            EIsZeroZero impossible
                                                                                            EIsZeroSucc impossible
                                                                                            (EIsZero _) impossible)
                                                                              (Succ nv) => (case x of
                                                                                                 (ESucc y) => valuesDontEvaluate {pf=ConvertedFrom (Right nv)} y)

||| Proof that the only derivation of a value term in the reflexive transitive of the `E`-evaluation rules
||| is the trivial derivation.
valuesAreNormal : {pf : IsValue v} -> (r : EvalsToStar v t) -> (r = (Refl {rel=EvalsTo} {x=v}))
valuesAreNormal (Refl {x}) = Refl
valuesAreNormal {pf} (Cons x y) with (valuesDontEvaluate {pf=pf} x)
  valuesAreNormal {pf} (Cons x y) | with_pat impossible

||| Proof that a value is either
|||
|||     1. `True`
|||     2. `False`
|||     3. `Zero`
|||     4. `Succ nv`, with `nv` a numeric value
valueIsEither : (v : Term) -> {pf : IsValue v} -> Either (v = True) (Either (v = False) (Either (v = Zero) (nv : Term ** ((v = Succ nv), IsNumValue nv))))
valueIsEither (bv2t x) {pf = (ConvertedFrom (Left x))} = case x of
                                                              True => Left Refl
                                                              False => Right (Left Refl)
valueIsEither (nv2t x) {pf = (ConvertedFrom (Right x))} = case x of
                                                               Zero => Right (Right (Left Refl))
                                                               (Succ y) => Right (Right (Right (nv2t y ** (Refl, ConvertedFrom y))))

||| Proof that a term of the form `Succ t` is only a value if `t` is a numeric value.
succIsValueIf : (pf : IsValue (Succ t)) ->
                IsNumValue t
succIsValueIf (ConvertedFrom (Left Values.True)) impossible
succIsValueIf (ConvertedFrom (Left Values.False)) impossible
succIsValueIf (ConvertedFrom (Right Values.Zero)) impossible
succIsValueIf (ConvertedFrom (Right (Succ nv))) = ConvertedFrom nv

||| Proof that a term of the form `Pred t` is never a value.
predNotValue : (pf : IsValue (Pred t)) -> Void
predNotValue (ConvertedFrom (Left Values.True)) impossible
predNotValue (ConvertedFrom (Left Values.False)) impossible
predNotValue (ConvertedFrom (Right Values.Zero)) impossible
predNotValue (ConvertedFrom (Right (Values.Succ nv))) impossible

||| Proof that a value only evaluates to itself under the reflexive transitive closure of
||| the `E`-evaluation rules.
valuesAreNormal' : {pf : IsValue v} ->
                   EvalsToStar v t ->
                   (t = v)
valuesAreNormal' {pf} x with (valuesAreNormal {pf=pf} x)
  valuesAreNormal' {pf} x | with_pat = case with_pat of
                                            Refl => Refl

||| Proof that a term of the form `IfThenElse x y z` is never a value.
ifThenElseNotNormal : (pf : IsValue (IfThenElse x y z)) -> Void
ifThenElseNotNormal {x} {y} {z} pf with (valueIsEither (IfThenElse x y z) {pf=pf})
  ifThenElseNotNormal {x} {y} {z} pf | (Left l) = case l of
                                                       Refl impossible
  ifThenElseNotNormal {x} {y} {z} pf | (Right (Left l)) = case l of
                                                               Refl impossible
  ifThenElseNotNormal {x} {y} {z} pf | (Right (Right (Left l))) = case l of
                                                                       Refl impossible
  ifThenElseNotNormal {x} {y} {z} pf | (Right (Right (Right (nv ** (pf1, pf2))))) = case pf1 of
                                                                                         Refl impossible

--------------------------------------------------------------------------------
-- Sublemmas of `from_E_to_BInE`
--------------------------------------------------------------------------------

lemma_EIfTrue : {pf : IsValue v} ->
                (d' : EvalsToStar t2 v) ->
                (r : BInE (IfThenElse True t2 t3) v ** Cons EIfTrue d' = from_BInE_to_E r)
lemma_EIfTrue {pf} d' = (BInEIfTrue {pf=pf} Refl d' ** Refl)

lemma_EIfFalse : {pf : IsValue v} ->
                 (d' : EvalsToStar t3 v) ->
                 (r : BInE (IfThenElse False t2 t3) v ** Cons EIfFalse d' = from_BInE_to_E r)
lemma_EIfFalse {pf} d' = (BInEIfFalse {pf=pf} Refl d' ** Refl)

lemma_EIf : {pf : IsValue v} ->
            {x : EvalsTo t1 t1'} ->
            (d' : EvalsToStar (IfThenElse t1' t2 t3) v) ->
            (r' : BInE (IfThenElse t1' t2 t3) v ** d' = from_BInE_to_E r') ->
            (r : BInE (IfThenElse t1 t2 t3) v ** Cons (EIf x) d' = from_BInE_to_E r)
lemma_EIf {pf} {x} d' (r' ** pf') = case r' of
                                         BInEValue {pf} => absurd (ifThenElseNotNormal pf)
                                         BInEIfTrue d1 d2 => (BInEIfTrue {pf=pf} (Cons x d1) d2 ** cong pf')
                                         BInEIfFalse d1 d2 => (BInEIfFalse {pf=pf} (Cons x d1) d2 ** cong pf')

lemma_ESucc : {pf : IsValue v} ->
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
