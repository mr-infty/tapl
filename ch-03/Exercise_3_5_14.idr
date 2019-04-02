module Exercise_3_5_14

import Arith

%default total

numValueProofIs : {t : Term} ->
                  (pf : IsNumValue t) ->
                  (nv : NumValue ** (t = nv2t nv, pf = ConvertedFrom nv))
numValueProofIs {t = (v2t (Right nv))} (ConvertedFrom nv) = (nv ** (Refl, Refl))

zeroNotSucc : {t : Term} ->
              (Zero = Succ t) -> Void
zeroNotSucc Refl impossible

succ_inj : {t1, t2 : Term} ->
           (Succ t1 = Succ t2) ->
           (t1 = t2)
succ_inj Refl = Refl

nv2t_inj : {nv1, nv2 : NumValue} ->
           (nv2t nv1 = nv2t nv2) ->
           (nv1 = nv2)
nv2t_inj {nv1=Zero} {nv2=Zero} prf = Refl
nv2t_inj {nv1=Zero} {nv2=Succ x} prf = absurd (zeroNotSucc prf)
nv2t_inj {nv1=Succ x} {nv2=Zero} prf = absurd (zeroNotSucc (sym prf))
nv2t_inj {nv1=Succ x} {nv2=Succ y} prf = cong (nv2t_inj (succ_inj prf))

numValueProofsUnique : {t : Term} ->
                       (pf1 : IsNumValue t) ->
                       (pf2 : IsNumValue t) ->
                       (pf1 = pf2)
numValueProofsUnique pf1 pf2 with (numValueProofIs pf1)
  numValueProofsUnique pf1 pf2 | (nv ** (pf_t, pf_pf)) with (numValueProofIs pf2)
    numValueProofsUnique pf1 pf2 | (nv ** (pf_t, pf_pf)) | (nv' ** (pf_t', pf_pf')) = case nv2t_inj {nv1=nv} {nv2=nv'} (trans (sym pf_t) pf_t') of
                                                                                           Refl => trans pf_pf (sym pf_pf')
uniqueEval : (t : Term) ->
             (r : EvalsTo t t') ->
             (r' : EvalsTo t t'') ->
             (r = r') 
uniqueEval True EIfTrue _ impossible
uniqueEval True EIfFalse _ impossible
uniqueEval True (EIf _) _ impossible
uniqueEval True (ESucc _) _ impossible
uniqueEval True EPredZero _ impossible
uniqueEval True EPredSucc _ impossible
uniqueEval True (EPred _) _ impossible
uniqueEval True EIsZeroZero _ impossible
uniqueEval True EIsZeroSucc _ impossible
uniqueEval True (EIsZero _) _ impossible
uniqueEval False EIfTrue _ impossible
uniqueEval False EIfFalse _ impossible
uniqueEval False (EIf _) _ impossible
uniqueEval False (ESucc _) _ impossible
uniqueEval False EPredZero _ impossible
uniqueEval False EPredSucc _ impossible
uniqueEval False (EPred _) _ impossible
uniqueEval False EIsZeroZero _ impossible
uniqueEval False EIsZeroSucc _ impossible
uniqueEval False (EIsZero _) _ impossible
uniqueEval (IfThenElse True y z) EIfTrue EIfTrue = Refl
uniqueEval (IfThenElse True y z) EIfTrue (EIf x) impossible
uniqueEval (IfThenElse False y z) EIfFalse EIfFalse = Refl
uniqueEval (IfThenElse False y z) EIfFalse (EIf x) impossible
uniqueEval (IfThenElse True y z) (EIf w) EIfTrue impossible
uniqueEval (IfThenElse False y z) (EIf w) EIfFalse impossible
uniqueEval (IfThenElse x y z) (EIf w) (EIf s) = case uniqueEval x w s of
                                                     Refl => Refl
uniqueEval Zero EIfTrue _ impossible
uniqueEval Zero EIfFalse _ impossible
uniqueEval Zero (EIf _) _ impossible
uniqueEval Zero (ESucc _) _ impossible
uniqueEval Zero EPredZero _ impossible
uniqueEval Zero EPredSucc _ impossible
uniqueEval Zero (EPred _) _ impossible
uniqueEval Zero EIsZeroZero _ impossible
uniqueEval Zero EIsZeroSucc _ impossible
uniqueEval Zero (EIsZero _) _ impossible
uniqueEval (Succ x) (ESucc y) (ESucc z) = case uniqueEval x y z of
                                               Refl => Refl
uniqueEval (Pred Zero) EPredZero EPredZero = Refl
uniqueEval (Pred Zero) EPredZero (EPred x) impossible
uniqueEval (Pred (Succ t')) (EPredSucc {pf=pf1}) (EPredSucc {pf=pf2}) = case numValueProofsUnique pf1 pf2 of
                                                                             Refl => Refl
uniqueEval (Pred (Succ t')) (EPredSucc {pf}) (EPred x) = absurd (valuesDontEvaluate {pf=(numValueIsValue (succNumValueIsNumValue pf))} x)
uniqueEval (Pred Zero) (EPred y) EPredZero = absurd (valuesDontEvaluate {pf=IsValue.ConvertedFrom (Right Zero)} y)
uniqueEval (Pred (Succ t')) (EPred y) (EPredSucc {pf}) = absurd (valuesDontEvaluate {pf=(numValueIsValue (succNumValueIsNumValue pf))} y)

uniqueEval (Pred x) (EPred y) (EPred z) = case uniqueEval x y z of
                                               Refl => Refl
uniqueEval (IsZero Zero) EIsZeroZero EIsZeroZero = Refl
uniqueEval (IsZero Zero) EIsZeroZero (EIsZero x) impossible
uniqueEval (IsZero (Succ nv1)) (EIsZeroSucc {pf=pf1}) (EIsZeroSucc {pf=pf2}) = case numValueProofsUnique pf1 pf2 of
                                                                                    Refl => Refl
uniqueEval (IsZero (Succ nv1)) (EIsZeroSucc {pf}) (EIsZero x) = absurd (valuesDontEvaluate {pf=(numValueIsValue (succNumValueIsNumValue pf))} x)
uniqueEval (IsZero Zero) (EIsZero y) EIsZeroZero impossible
uniqueEval (IsZero (Succ nv1)) (EIsZero y) (EIsZeroSucc {pf}) = absurd (valuesDontEvaluate {pf=(numValueIsValue (succNumValueIsNumValue pf))} y)
uniqueEval (IsZero x) (EIsZero y) (EIsZero z) = case uniqueEval x y z of
                                                     Refl => Refl

||| Proof that the one-step evaluation rules of the arithmetic language are deterministic (Ex. 3.5.14).
detVal : {t,t',t'' : Term} ->
         EvalsTo t t' ->
         EvalsTo t t'' ->
         (t' = t'')
detVal {t} pf pf' = case uniqueEval t pf pf' of
                         Refl => Refl
