module Ch03.Arith

%default total
%access public export

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

namespace IsBoolValue
  ||| Propositional type describing that a term "is" indeed a boolean value
  data IsBoolValue : Term -> Type where
    ConvertedFrom : (bv : BoolValue) -> IsBoolValue (v2t (Left bv))

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
-- Some properties of values and evaluation
--------------------------------------------------------------------------------

||| A numeric value is also a value
numValueIsValue : IsNumValue t -> IsValue t
numValueIsValue {t = (v2t (Right nv))} (ConvertedFrom nv) = IsValue.ConvertedFrom (Right nv)

||| The successor of a numeric value is a numeric value
succNumValueIsNumValue : IsNumValue t -> IsNumValue (Succ t)
succNumValueIsNumValue {t = (v2t (Right nv))} (ConvertedFrom nv) = ConvertedFrom (Succ nv)

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
succIsValueIf : IsValue (Succ t) -> IsNumValue t
succIsValueIf (ConvertedFrom (Left Values.True)) impossible
succIsValueIf (ConvertedFrom (Left Values.False)) impossible
succIsValueIf (ConvertedFrom (Right Values.Zero)) impossible
succIsValueIf (ConvertedFrom (Right (Succ nv))) = ConvertedFrom nv

||| Proof that a term of the form `Pred t` is never a value.
predNotValue : IsValue (Pred t) -> Void
predNotValue (ConvertedFrom (Left Values.True)) impossible
predNotValue (ConvertedFrom (Left Values.False)) impossible
predNotValue (ConvertedFrom (Right Values.Zero)) impossible
predNotValue (ConvertedFrom (Right (Values.Succ nv))) impossible

||| Proof that a term of the form `IsZero t` is never a value.
isZeroNotValue : IsValue (IsZero t) -> Void
isZeroNotValue (ConvertedFrom (Left Values.True)) impossible
isZeroNotValue (ConvertedFrom (Left Values.False)) impossible
isZeroNotValue (ConvertedFrom (Right Values.Zero)) impossible
isZeroNotValue (ConvertedFrom (Right (Values.Succ nv))) impossible

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
