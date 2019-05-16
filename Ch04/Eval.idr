module Ch04.Eval

import Ch03.Arith
import Data.Fin

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
    EPredWrong : {t : Term} ->
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

||| Propositional type describing that a term is normal.
Normal : Term -> Type
Normal t = (t' : Term) -> EvalsTo t t' -> Void

--------------------------------------------------------------------------------
-- Helper lemmas for `fully_evaluated_is_normal`.
--------------------------------------------------------------------------------

true_is_normal : Normal True
true_is_normal = \_, r => case r of
                               EIfTrue impossible
                               EIfFalse impossible
                               (EIf _) impossible
                               (ESucc _) impossible
                               EPredZero impossible
                               EPredSucc impossible
                               (EPred _) impossible
                               EIsZeroZero impossible
                               EIsZeroSucc impossible
                               (EIsZero _) impossible

false_is_normal : Normal False
false_is_normal = \_, r => case r of
                                EIfTrue impossible
                                EIfFalse impossible
                                (EIf _) impossible
                                (ESucc _) impossible
                                EPredZero impossible
                                EPredSucc impossible
                                (EPred _) impossible
                                EIsZeroZero impossible
                                EIsZeroSucc impossible
                                (EIsZero _) impossible

zero_is_normal : Normal Zero
zero_is_normal = \_, r => case r of
                               EIfTrue impossible
                               EIfFalse impossible
                               (EIf _) impossible
                               (ESucc _) impossible
                               EPredZero impossible
                               EPredSucc impossible
                               (EPred _) impossible
                               EIsZeroZero impossible
                               EIsZeroSucc impossible
                               (EIsZero _) impossible

num_values_are_normal_helper : (nv : NumValue) -> Normal (nv2t nv)
num_values_are_normal_helper nv = case nv of
                                       Zero => zero_is_normal
                                       (Succ nv') => \_, r => case r of
                                                                    (ESucc r') => (num_values_are_normal_helper nv') _ r'

num_values_are_normal : (t : Term) -> {pf : IsNumValue t} -> Normal t
num_values_are_normal (nv2t nv) {pf=ConvertedFrom nv} = num_values_are_normal_helper nv


values_are_normal : (t : Term) -> {pf : IsValue t} -> Normal t
values_are_normal (bv2t bv) {pf=ConvertedFrom (Left bv)} = case bv of
                                                                True => true_is_normal
                                                                False => false_is_normal
values_are_normal (nv2t nv) {pf=ConvertedFrom (Right nv)} = num_values_are_normal (nv2t nv) {pf=ConvertedFrom nv}

values_not_stuck : {t : Term} -> {pf : IsValue t} -> Not (IsStuck t)

bool_not_bad_bool : {t : Term} -> {pf : IsBoolValue t} -> Not (IsBadBool t)
bool_not_bad_bool {pf} = \x => case x of
                                    IsStuckTerm {pf=pf_stuck} => (values_not_stuck {pf=boolValueIsValue pf}) pf_stuck
                                    IsNat {pf=pf_nat} => numNotBool pf_nat pf

nat_not_bad_nat : {t : Term} -> {pf : IsNumValue t} -> Not (IsBadNat t)
nat_not_bad_nat {pf} = \x => case x of
                                  IsStuckTerm {pf=pf_stuck} => (values_not_stuck {pf=numValueIsValue pf}) pf_stuck
                                  IsBool {pf=pf_bool} => numNotBool pf pf_bool

stuck_is_normal : IsStuck t -> Normal t
stuck_is_normal (EIfWrong {pf}) = \_, r => case r of
                                                EIfTrue => (bool_not_bad_bool {pf=ConvertedFrom True}) pf
                                                EIfFalse => (bool_not_bad_bool {pf=ConvertedFrom False}) pf
                                                (EIf {t1} r') => case pf of
                                                                      IsStuckTerm {pf=pf_stuck} => stuck_is_normal pf_stuck _ r'
                                                                      IsNat {pf=pf_num} => values_are_normal t1 {pf=numValueIsValue pf_num} _ r'
stuck_is_normal (ESuccWrong {t} {pf}) = \_, r => case r of
                                                      (ESucc r') => case pf of
                                                                         IsStuckTerm {pf=pf_stuck} => stuck_is_normal pf_stuck _ r'
                                                                         IsBool {pf=pf_bool} => values_are_normal t {pf=boolValueIsValue pf_bool} _ r'
stuck_is_normal (EPredWrong {t} {pf}) = \_, r => case r of
                                                      EPredZero => nat_not_bad_nat {pf=ConvertedFrom Zero} pf
                                                      EPredSucc {nv1=nv} {pf=pf_num} => nat_not_bad_nat {pf=succNumValueIsNumValue pf_num} pf
                                                      (EPred r') => case pf of
                                                                         IsStuckTerm {pf=pf_stuck} => stuck_is_normal pf_stuck _ r'
                                                                         IsBool {pf=pf_bool} => values_are_normal t {pf=boolValueIsValue pf_bool} _ r'
stuck_is_normal (EIsZeroWrong {t} {pf}) = \_, r => case r of
                                                        EIsZeroZero => nat_not_bad_nat {pf=ConvertedFrom Zero} pf
                                                        EIsZeroSucc {nv1=nv} {pf=pf_num} => nat_not_bad_nat {pf=succNumValueIsNumValue pf_num} pf
                                                        (EIsZero r') => case pf of
                                                                             IsStuckTerm {pf=pf_stuck} => stuck_is_normal pf_stuck _ r'
                                                                             IsBool {pf=pf_bool} => values_are_normal t {pf=boolValueIsValue pf_bool} _ r'

||| Proof that a fully evaluated term is also normal.
fully_evaluated_is_normal : FullyEvaluated t -> Normal t
fully_evaluated_is_normal (Left pf_stuck) = stuck_is_normal pf_stuck
fully_evaluated_is_normal {t} (Right pf_value) = values_are_normal t {pf=pf_value}

-----------------------------------------------------------------------
-- Helper lemmas for `normal_is_fully_evaluated`.
-----------------------------------------------------------------------

if_subterm_of_normal_is_normal : {x,y,z : Term} -> Normal (IfThenElse x y z) -> Normal x
if_subterm_of_normal_is_normal pf = \_, r => absurd (pf _ (EIf r))

succ_subterm_of_normal_is_normal : {t : Term} -> Normal (Succ t) -> Normal t
succ_subterm_of_normal_is_normal pf = \_, r => absurd (pf _ (ESucc r))

pred_subterm_of_normal_is_normal : {t : Term} -> Normal (Pred t) -> Normal t
pred_subterm_of_normal_is_normal pf = \_, r => absurd (pf _ (EPred r))

is_zero_subterm_of_normal_is_normal : {t : Term} -> Normal (IsZero t) -> Normal t
is_zero_subterm_of_normal_is_normal pf = \_, r => absurd (pf _ (EIsZero r))

succ_of_fully_evaluated_is_fully_evaluated : {t : Term} -> FullyEvaluated t -> FullyEvaluated (Succ t)
succ_of_fully_evaluated_is_fully_evaluated {t} (Left pf_stuck) = Left (ESuccWrong {pf=IsStuckTerm {pf=pf_stuck}})
succ_of_fully_evaluated_is_fully_evaluated {t} (Right pf_val) = case pf_val of
                                                                     ConvertedFrom (Left bv) => Left (ESuccWrong {pf=IsBool {pf=ConvertedFrom bv}})
                                                                     ConvertedFrom (Right nv) => Right (numValueIsValue $ succNumValueIsNumValue (ConvertedFrom nv))

||| Proof that a normal term is also fully evaluated.
normal_is_fully_evaluated : Normal t -> FullyEvaluated t
normal_is_fully_evaluated {t=True} _ = Right (ConvertedFrom (Left True))
normal_is_fully_evaluated {t=False} _ = Right (ConvertedFrom (Left False))
normal_is_fully_evaluated {t=IfThenElse t1 t2 t3} pf_normal = case normal_is_fully_evaluated (if_subterm_of_normal_is_normal pf_normal) of
                                                                   (Left pf_stuck) => Left (EIfWrong {pf=IsStuckTerm {pf=pf_stuck}})
                                                                   (Right pf_val) => case pf_val of
                                                                                          (ConvertedFrom (Left bv)) => case bv of
                                                                                                                            True => absurd (pf_normal _ EIfTrue)
                                                                                                                            False => absurd (pf_normal _ EIfFalse)
                                                                                          (ConvertedFrom (Right nv)) => Left (EIfWrong {pf=IsNat {pf=ConvertedFrom nv}})
normal_is_fully_evaluated {t=Zero} _ = Right (ConvertedFrom (Right Zero))
normal_is_fully_evaluated {t=Succ t'} pf_normal = succ_of_fully_evaluated_is_fully_evaluated $
                                                  normal_is_fully_evaluated $
                                                  succ_subterm_of_normal_is_normal pf_normal
normal_is_fully_evaluated {t=Pred t'} pf_normal = case normal_is_fully_evaluated $ pred_subterm_of_normal_is_normal pf_normal of
                                                       Left pf_stuck => Left (EPredWrong {pf=IsStuckTerm {pf=pf_stuck}})
                                                       Right pf_val => case pf_val of
                                                                            (ConvertedFrom (Left bv)) => Left (EPredWrong {pf=IsBool {pf=ConvertedFrom bv}})
                                                                            (ConvertedFrom (Right Zero)) => absurd (pf_normal _ EPredZero)
                                                                            (ConvertedFrom (Right (Succ nv))) => absurd (pf_normal _ (EPredSucc {pf=ConvertedFrom nv}))
normal_is_fully_evaluated {t=IsZero t'} pf_normal = case normal_is_fully_evaluated $ is_zero_subterm_of_normal_is_normal pf_normal of
                                                         Left pf_stuck => Left (EIsZeroWrong {pf=IsStuckTerm {pf=pf_stuck}})
                                                         Right pf_val => case pf_val of
                                                                              (ConvertedFrom (Left bv)) => Left (EIsZeroWrong {pf=IsBool {pf=ConvertedFrom bv}})
                                                                              (ConvertedFrom (Right Zero)) => absurd (pf_normal _ EIsZeroZero)
                                                                              (ConvertedFrom (Right (Succ nv))) => absurd (pf_normal _ (EIsZeroSucc {pf=ConvertedFrom nv}))

--------------------------------------------------------------------------------
-- Definition of the evaluation function.
--------------------------------------------------------------------------------

eval_reduces_size : {t,t' : Term} -> EvalsTo t t' -> (k : Fin (size t) ** size t' = finToNat k)

either_normal_or_evals : (t : Term) -> Either (Normal t) (t' : Term ** EvalsTo t t')

||| Given a term, returns its value.
smallStep_eval : (t : Term) -> (v : Term ** (EvalsToStar t v, FullyEvaluated v))
smallStep_eval t = ?smallStep_eval_rhs

