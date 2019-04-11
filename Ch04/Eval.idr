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
Normal t = {t' : Term} -> EvalsTo t t' -> Void

true_is_normal : Normal True
true_is_normal = \r => case r of
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
false_is_normal = \r => case r of
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
zero_is_normal = \r => case r of
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

num_values_are_normal : (t : Term) -> {pf : IsNumValue t} -> Normal t
num_values_are_normal (nv2t nv) {pf=ConvertedFrom nv} = case nv of
                                                             Zero => zero_is_normal
                                                             (Succ nv') => \r => case r of
                                                                                      (ESucc r') => (num_values_are_normal (nv2t nv') {pf=ConvertedFrom nv'}) r'

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

stuck_is_normal : IsStuck t -> Normal t
stuck_is_normal (EIfWrong {pf}) = \r => case r of
                                             EIfTrue => (bool_not_bad_bool {pf=ConvertedFrom True}) pf
                                             EIfFalse => (bool_not_bad_bool {pf=ConvertedFrom False}) pf
                                             (EIf {t1} r') => case pf of
                                                                   IsStuckTerm {pf=pf_stuck} => (stuck_is_normal pf_stuck) r'
                                                                   IsNat {pf=pf_num} => values_are_normal t1 {pf=numValueIsValue pf_num} r'
stuck_is_normal ESuccWrong = ?stuck_is_normal_rhs_2
stuck_is_normal EPredWrong = ?stuck_is_normal_rhs_3
stuck_is_normal EIsZeroWrong = ?stuck_is_normal_rhs_4

fully_evaluated_is_normal : FullyEvaluated t -> Normal t
fully_evaluated_is_normal (Left pf_stuck) = stuck_is_normal pf_stuck
fully_evaluated_is_normal (Right pf_value) = ?fully_evaluated_is_normal_rhs_2

normal_is_fully_evaluated : Normal t -> FullyEvaluated t

||| Given a term, returns its value.
smallStep_eval : (t : Term) -> (v : Term ** (EvalsToStar t v, FullyEvaluated v))
smallStep_eval t = ?smallStep_eval_rhs
