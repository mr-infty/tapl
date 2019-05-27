module Ch04.NaturalInduction

-- TODO: Figure out how to implement the function below (if it's at all possible).

--natural_induction_principle : {a,b : Type} -> 
--                              (size : a -> Nat) ->
--                              (f : (x : a) -> Either b (x' : a ** LT (size x') (size x))) ->
--                              (g : (a -> b) ** (x : a) -> (case f x of
--                                                                Left y => (g x = y)
--                                                                Right (y ** _) => (g x = g y)))

lemma : {x : Nat} ->
        LTE x 0 ->
        (x = 0)
lemma {x = Z} pf = Refl
lemma {x = (S k)} pf = absurd (succNotLTEzero pf)

public export
inductive_construction : {a,b : Type} ->
                         (size : a -> Nat) ->
                         (f : (x : a) -> Either b (x' : a ** LT (size x') (size x))) ->
                         a -> b
inductive_construction {a} {b} size f x = helper x (size x) lteRefl where
  helper : (x : a) -> (k : Nat) -> LTE (size x) k -> b
  helper x k bound = case f x of
                          Left y => y
                          Right (x' ** pf) => case k of
                                                    Z => let temp = replace (lemma bound) pf in
                                                             absurd (succNotLTEzero temp)
                                                    (S j) => helper x' j (fromLteSucc (lteTransitive pf bound))
