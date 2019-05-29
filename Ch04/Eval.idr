module Ch04.Eval

import Ch03.Arith
import Ch04.NaturalInduction
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

num_value_not_bool_value : (nv : NumValue) -> Not (IsBoolValue (nv2t nv))
num_value_not_bool_value Zero = \pf_bv => case pf_bv of
                                               ConvertedFrom True impossible
                                               ConvertedFrom False impossible
num_value_not_bool_value (Succ nv) = \pf_bv => case pf_bv of
                                                    (ConvertedFrom True) impossible
                                                    (ConvertedFrom False) impossible

num_value_not_stuck : (nv : NumValue) -> Not (IsStuck (nv2t nv))
num_value_not_stuck Zero = \pf_bad => case pf_bad of
                                           EIfWrong impossible
                                           ESuccWrong impossible
                                           EPredWrong impossible
                                           EIsZeroWrong impossible
num_value_not_stuck (Succ nv) = \pf_bad => case pf_bad of
                                                ESuccWrong {pf=pf_succ_wrong} => case pf_succ_wrong of
                                                                                      IsStuckTerm {pf=pf_stuck} => absurd ((num_value_not_stuck nv) pf_stuck)
                                                                                      IsBool {pf=pf_bool} => absurd ((num_value_not_bool_value nv) pf_bool)

num_value_not_bad_nat : (nv : NumValue) -> Not (IsBadNat (nv2t nv))
num_value_not_bad_nat nv = \pf_bad => case pf_bad of
                                           IsStuckTerm {pf=pf_stuck} => absurd ((num_value_not_stuck nv) pf_stuck)
                                           IsBool {pf=pf_bool} => absurd ((num_value_not_bool_value nv) pf_bool)

values_not_stuck : {t : Term} -> {pf : IsValue t} -> Not (IsStuck t)
values_not_stuck {t = (bv2t bv)} {pf = (ConvertedFrom (Left bv))} = \pf_stuck => case bv of
                                                                                      True => case pf_stuck of
                                                                                                   EIfWrong impossible
                                                                                                   ESuccWrong impossible
                                                                                                   EPredWrong impossible
                                                                                                   EIsZeroWrong impossible
                                                                                      False => case pf_stuck of
                                                                                                    EIfWrong impossible
                                                                                                    ESuccWrong impossible
                                                                                                    EPredWrong impossible
                                                                                                    EIsZeroWrong impossible
values_not_stuck {t = (nv2t nv)} {pf = (ConvertedFrom (Right nv))} = num_value_not_stuck nv

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

eval_reduces_size_lemma1 : {n,m : Nat} ->
                           LTE (S n) (S ((n + m) + 1))
eval_reduces_size_lemma1 {n = Z} = LTESucc LTEZero
eval_reduces_size_lemma1 {n = (S k)} = LTESucc (eval_reduces_size_lemma1 {n=k})

eval_reduces_size_lemma2 : {n,m : Nat} ->
                           LTE (S m) (S ((n + m) + 1))
eval_reduces_size_lemma2 {n} {m} = rewrite plusCommutative n m in
                                           eval_reduces_size_lemma1

eval_reduces_size_lemma3 : {n,m,l : Nat} ->
                           LTE n m ->
                           LTE (l+n) (l+m)
eval_reduces_size_lemma3 {l = Z} pf = pf
eval_reduces_size_lemma3 {l = (S k)} pf = LTESucc (eval_reduces_size_lemma3 pf)

eval_reduces_size_lemma3' : {n,m,l : Nat} ->
                            LTE n m ->
                            LTE (n+l) (m+l)
eval_reduces_size_lemma3' {n} {m} {l} pf = rewrite plusCommutative n l in
                                                   rewrite plusCommutative m l in
                                                           eval_reduces_size_lemma3 pf

data ElementaryMonotoneFunction : (Nat -> Nat) -> Type where
  IsConstant : {c : Nat} -> ElementaryMonotoneFunction (const c)
  IsIdentity : ElementaryMonotoneFunction (\n => n) --TODO: Figure out why using `id {a=Nat}` fails to type check
  IsSum : {f,g : Nat -> Nat} ->
          ElementaryMonotoneFunction f ->
          ElementaryMonotoneFunction g ->
          ElementaryMonotoneFunction (\n => (f n) + (g n))

namespace ElementaryStrictlyMonotoneFunction
  data ElementaryStrictlyMonotoneFunction : (Nat -> Nat) -> Type where
    IsIdentity : ElementaryStrictlyMonotoneFunction (\n => n)
    IsSumLeft : {f,g : Nat -> Nat} ->
                ElementaryStrictlyMonotoneFunction f ->
                ElementaryMonotoneFunction g ->
                ElementaryStrictlyMonotoneFunction (\n => (f n) + (g n))
    IsSumRight : {f,g : Nat -> Nat} ->
                 ElementaryMonotoneFunction f ->
                 ElementaryStrictlyMonotoneFunction g ->
                 ElementaryStrictlyMonotoneFunction (\n => (f n) + (g n))

interface Monotone (P : (Nat -> Nat) -> Type) where
  monotone : (x, y : Nat) ->
             {f : Nat -> Nat} ->
             {pf : P f} ->
             LTE x y ->
             LTE (f x) (f y)

interface StrictlyMonotone (P : (Nat -> Nat) -> Type) where
  strictly_monotone : (x, y : Nat) ->
                      {f : Nat -> Nat} ->
                      {pf : P f} ->
                      LT x y ->
                      LT (f x) (f y)

Monotone ElementaryMonotoneFunction where
  monotone x y {f = (const c)} {pf = (IsConstant {c=c})} pf_assum = lteRefl
  monotone x y {f = (\n => n)} {pf = IsIdentity} pf_assum = pf_assum
  monotone x y {f = (\n => ((f n) + (g n)))} {pf = (IsSum {f} {g} pf_f pf_g)} pf_assum = let pf_assum_f = monotone x y {f=f} {pf=pf_f} pf_assum
                                                                                             pf_assum_g = monotone x y {f=g} {pf=pf_g} pf_assum
                                                                                             temp1 = eval_reduces_size_lemma3 {l=f x} pf_assum_g
                                                                                             temp2 = eval_reduces_size_lemma3' {l=g y} pf_assum_f in
                                                                                             lteTransitive temp1 temp2

StrictlyMonotone ElementaryStrictlyMonotoneFunction where
  strictly_monotone x y {f = (\n => n)} {pf = IsIdentity} pf_assum = pf_assum
  strictly_monotone x y {f = (\n => ((f n) + (g n)))} {pf = (IsSumLeft {f} {g} pf_f pf_g)} pf_assum = let pf_assum_f = strictly_monotone x y {f=f} {pf=pf_f} pf_assum
                                                                                                          pf_assum' = lteTransitive (lteSuccRight lteRefl) pf_assum
                                                                                                          pf_assum_g = monotone x y {f=g} {pf=pf_g} pf_assum'
                                                                                                          temp1 = eval_reduces_size_lemma3 {l=f y} pf_assum_g
                                                                                                          temp2 = eval_reduces_size_lemma3' {l=g x} pf_assum_f in
                                                                                                          lteTransitive temp2 temp1
  strictly_monotone x y {f = (\n => ((f n) + (g n)))} {pf = (IsSumRight {f} {g} pf_f pf_g)} pf_assum = let pf_assum_g = strictly_monotone x y {f=g} {pf=pf_g} pf_assum
                                                                                                           pf_assum' = lteTransitive (lteSuccRight lteRefl) pf_assum
                                                                                                           pf_assum_f = monotone x y {f=f} {pf=pf_f} pf_assum'
                                                                                                           temp1 = eval_reduces_size_lemma3 {l=f x} pf_assum_g
                                                                                                           temp2 = eval_reduces_size_lemma3' {l=g y} pf_assum_f in
                                                                                                           rewrite plusSuccRightSucc (f x) (g x) in
                                                                                                                   lteTransitive temp1 temp2

-- Note: We need to define `if_then_else_size_f` explicitly using a lambda expression
-- (instead of pattern matching) because otherwise `pf_if_then_else_size_f` below will
-- fail to type check.
if_then_else_size_f : {n2, n3 : Nat} -> Nat -> Nat
if_then_else_size_f {n2} {n3} = \n => ((n + n2) + n3) + 1

pf_if_then_else_size_f : {n2, n3 : Nat} ->
                         ElementaryStrictlyMonotoneFunction (if_then_else_size_f {n2=n2} {n3=n3})
pf_if_then_else_size_f {n2} {n3} = IsSumLeft (IsSumLeft (IsSumLeft IsIdentity (IsConstant {c=n2})) (IsConstant {c=n3})) (IsConstant {c=1})

succ_size_f : Nat -> Nat
succ_size_f = \n => S n

pf_succ_size_f : ElementaryStrictlyMonotoneFunction Ch04.Eval.succ_size_f
pf_succ_size_f = IsSumRight (IsConstant {c=1}) IsIdentity

pred_size_f : Nat -> Nat
pred_size_f = \n => S n

pf_pred_size_f : ElementaryStrictlyMonotoneFunction Ch04.Eval.pred_size_f
pf_pred_size_f = IsSumRight (IsConstant {c=1}) IsIdentity

is_zero_size_f : Nat -> Nat
is_zero_size_f = \n => S n

pf_is_zero_size_f : ElementaryStrictlyMonotoneFunction Ch04.Eval.is_zero_size_f
pf_is_zero_size_f = IsSumRight (IsConstant {c=1}) IsIdentity

||| Proof that evaluation reduces size.
eval_reduces_size : {t,t' : Term} -> EvalsTo t t' -> LT (size t') (size t)
eval_reduces_size {t = (IfThenElse True t2 t3)} {t' = t2} EIfTrue = eval_reduces_size_lemma1
eval_reduces_size {t = (IfThenElse False t2 t3)} {t' = t3} EIfFalse = eval_reduces_size_lemma2
eval_reduces_size {t = (IfThenElse t1 t2 t3)} {t' = (IfThenElse t1' t2 t3)} (EIf x) = let pf = eval_reduces_size x in
                                                                                          strictly_monotone (size t1') (size t1) {pf=pf_if_then_else_size_f} pf
eval_reduces_size {t = (Succ t1)} {t' = (Succ t2)} (ESucc x) = let pf = eval_reduces_size x in
                                                                   strictly_monotone (size t2) (size t1) {pf=pf_succ_size_f} pf
eval_reduces_size {t = (Pred Zero)} {t' = Zero} EPredZero = lteRefl
eval_reduces_size {t = (Pred (Succ t'))} {t' = t'} EPredSucc = LTESucc (lteSuccRight lteRefl)
eval_reduces_size {t = (Pred t1)} {t' = (Pred t2)} (EPred x) = let pf = eval_reduces_size x in
                                                                   strictly_monotone (size t2) (size t1) {pf=pf_pred_size_f} pf
eval_reduces_size {t = (IsZero Zero)} {t' = True} EIsZeroZero = lteRefl
eval_reduces_size {t = (IsZero (Succ nv1))} {t' = False} EIsZeroSucc = LTESucc (LTESucc LTEZero)
eval_reduces_size {t = (IsZero t1)} {t' = (IsZero t2)} (EIsZero x) = let pf = eval_reduces_size x in
                                                                         strictly_monotone (size t2) (size t1) {pf=pf_is_zero_size_f} pf

||| Proof that a term is either normal or evaluates to something. Note that this would be
||| a triviality if we were to assume the law of the excluded middle.
either_normal_or_evals : (t : Term) -> Either (Normal t) (t' : Term ** EvalsTo t t')
either_normal_or_evals True = Left true_is_normal
either_normal_or_evals False = Left false_is_normal
either_normal_or_evals (IfThenElse t1 t2 t3) = case either_normal_or_evals t1 of
                                                    Left pf_normal => case normal_is_fully_evaluated pf_normal of
                                                                           Left pf_stuck => Left (fully_evaluated_is_normal $
                                                                                           Left (EIfWrong {pf=IsStuckTerm {pf=pf_stuck}}))
                                                                           Right pf_val => case pf_val of
                                                                                                (ConvertedFrom (Left True)) => Right (t2 ** EIfTrue)
                                                                                                (ConvertedFrom (Left False)) => Right (t3 ** EIfFalse)
                                                                                                (ConvertedFrom (Right nv)) => Left (fully_evaluated_is_normal $
                                                                                                                             Left (EIfWrong {pf=IsNat {pf=ConvertedFrom nv}}))
                                                    Right (t1' ** r) => Right ((IfThenElse t1' t2 t3) ** EIf r)
either_normal_or_evals Zero = Left zero_is_normal
either_normal_or_evals (Succ t) = case either_normal_or_evals t of
                                       Left pf_normal => Left (fully_evaluated_is_normal $
                                                        succ_of_fully_evaluated_is_fully_evaluated $
                                                        normal_is_fully_evaluated pf_normal)
                                       Right (t' ** r) => Right ((Succ t') ** (ESucc r))
either_normal_or_evals (Pred t) = case either_normal_or_evals t of
                                       Left pf_normal => case normal_is_fully_evaluated pf_normal of
                                                              Left pf_stuck => Left (fully_evaluated_is_normal $
                                                                              Left (EPredWrong {pf=IsStuckTerm {pf=pf_stuck}}))
                                                              Right pf_val => case pf_val of
                                                                                   (ConvertedFrom (Left bv)) => Left (fully_evaluated_is_normal $
                                                                                                               Left (EPredWrong {pf=IsBool {pf=ConvertedFrom bv}}))
                                                                                   (ConvertedFrom (Right Zero)) => Right (Zero ** EPredZero)
                                                                                   (ConvertedFrom (Right (Succ nv))) => Right ((nv2t nv) ** EPredSucc {pf=ConvertedFrom nv})
                                       Right (t' ** r) => Right (_ ** (EPred r))
either_normal_or_evals (IsZero t) = case either_normal_or_evals t of
                                         Left pf_normal => case normal_is_fully_evaluated pf_normal of
                                                                Left pf_stuck => Left (fully_evaluated_is_normal $
                                                                                Left (EIsZeroWrong {pf=IsStuckTerm {pf=pf_stuck}}))
                                                                Right pf_val => case pf_val of
                                                                                     (ConvertedFrom (Left bv)) => Left (fully_evaluated_is_normal $
                                                                                                                 Left (EIsZeroWrong {pf=IsBool {pf=ConvertedFrom bv}}))
                                                                                     (ConvertedFrom (Right Zero)) => Right (True ** EIsZeroZero)
                                                                                     (ConvertedFrom (Right (Succ nv))) => Right (False ** EIsZeroSucc {pf=ConvertedFrom nv})
                                         Right (t' ** r) => Right (_ ** (EIsZero r))

||| Given a term, returns its value.
smallStep_eval : (t : Term) -> (v : Term ** (EvalsToStar t v, FullyEvaluated v))
smallStep_eval t = (inductive_construction size' f) (t ** Refl) where
  a : Type
  a = (t' : Term ** EvalsToStar t t')

  b : Type
  b = (t' : Term ** (EvalsToStar t t', FullyEvaluated t'))

  size' : a -> Nat
  size' (t' ** _) = size t'

  f : (x : a) -> Either b (x' : a ** LT (size' x') (size' x))
  f (t' ** p) = case either_normal_or_evals t' of
                     Left pf_normal => Left (t' ** (p, normal_is_fully_evaluated pf_normal))
                     Right (t'' ** p') => Right ((t'' ** (snoc p p')) ** eval_reduces_size p')


