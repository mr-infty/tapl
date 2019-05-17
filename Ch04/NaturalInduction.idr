module Ch04.NaturalInduction

import Data.So

--natural_induction_principle : {a,b : Type} -> 
--                              (size : a -> Nat) ->
--                              (f : (x : a) -> Either b (x' : a ** So (size x' < size x))) ->
--                              (g : (a -> b) ** (x : a) -> (case f x of
--                                                                Left y => (g x = y)
--                                                                Right (x' ** _) => (g x = g x')))

fixed_point_principle : {a : Type} ->
                        {b : a -> Type} ->
                        (size : a -> Nat) ->
                        (f : (x : a) -> Either (b x) (x' : a ** So (size x' < size x))) ->
                        (g : (a -> a) ** ((x : a) -> b (g x)))
fixed_point_principle {a} {b} size f = (g ** pf) where
  g_helper : (k : Nat) -> (x : a) -> (size x = k) -> a
  g_helper Z x prf = case f x of
                          Left pf_b => ?g_helper_rhs_3
                          Right (x' ** pf_smaller) => ?g_helper_rhs_4
  g_helper (S k) x prf = ?g_helper_rhs_2

  g : a -> a
  
  pf : (x : a) -> b (g x)
