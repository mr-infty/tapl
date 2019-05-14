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

-- We are using an ad hoc definition of what it means to be stuck,
-- which is not exactly the one used in the book (normal but not a value).
-- This is for convenience. (TODO: Fix this maybe.)
||| Propositional type describing that a term is fully evaluated.
FullyEvaluated : Term -> Type
FullyEvaluated t = Either (IsStuck t) (IsValue t)

||| Propositional type describing that a term is normal.
Normal : Term -> Type
Normal t = (t' : Term) -> EvalsTo t t' -> Void

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

||| Proof that a fully evaluated terms is also normal.
fully_evaluated_is_normal : FullyEvaluated t -> Normal t
fully_evaluated_is_normal (Left pf_stuck) = stuck_is_normal pf_stuck
fully_evaluated_is_normal {t} (Right pf_value) = values_are_normal t {pf=pf_value}

||| Proof that a direct subterm of a normal term is normal.
direct_subterm_of_normal_is_normal : {t1,t2 : Term} -> DirectSubTerm t1 t2 -> Normal t2 -> Normal t1
direct_subterm_of_normal_is_normal (IsIfTerm x) pf = ?f_hole where
  f : {t' : Term} -> EvalsTo x t' -> Void
  f {t'=ymca} = ?hole--absurd {t = Void} (pf (EIf ?subterm_of_normal_is_normal_rhs_1))
direct_subterm_of_normal_is_normal (IsThenTerm y) pf = ?subterm_of_normal_is_normal_rhs_2
direct_subterm_of_normal_is_normal (IsElseTerm z) pf = ?subterm_of_normal_is_normal_rhs_3
direct_subterm_of_normal_is_normal (IsSuccSubTerm x) pf = ?subterm_of_normal_is_normal_rhs_4
direct_subterm_of_normal_is_normal (IsPredSubTerm x) pf = ?subterm_of_normal_is_normal_rhs_5

||| Proof that a normal term is also fully evaluated.
normal_is_fully_evaluated : Normal t -> FullyEvaluated t
normal_is_fully_evaluated {t=True} _ = Right (ConvertedFrom (Left True))
normal_is_fully_evaluated {t=False} _ = Right (ConvertedFrom (Left False))
normal_is_fully_evaluated {t=IfThenElse t1 t2 t3} pf_normal = ?normal_is_fully_evaluated_rhs_3
normal_is_fully_evaluated {t=Zero} _ = Right (ConvertedFrom (Right Zero))
normal_is_fully_evaluated {t=Succ t'} pf_normal = ?normal_is_fully_evaluated_rhs_5
normal_is_fully_evaluated {t=Pred t'} pf_normal = ?normal_is_fully_evaluated_rhs_6
normal_is_fully_evaluated {t=IsZero t'} pf_normal = ?normal_is_fully_evaluated_rhs_7

||| Given a term, returns its value.
smallStep_eval : (t : Term) -> (v : Term ** (EvalsToStar t v, FullyEvaluated v))
smallStep_eval t = ?smallStep_eval_rhs

