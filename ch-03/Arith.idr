module Arith

data Term = True
          | False
          | IfThenElse Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term

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

Value : Type
Value = Either Nat Bool

eval : Term -> Value
eval True = Right True
eval False = Right True
eval (IfThenElse x y z) = case eval x of
                               (Left l) => if l /= 0
                                              then eval y
                                              else eval z
                               (Right r) => if r
                                               then eval y
                                               else eval z
eval Zero = Left 0
eval (Succ x) = case eval x of
                     (Left l) => Left (S l)
                     (Right r) => ?eval_rhs_2
eval (Pred x) = case eval x of
                     (Left l) => Left (pred l)
                     (Right r) => ?eval_rhs_4
eval (IsZero x) = case eval x of
                       (Left l) => Right (l == 0)
                       (Right r) => ?eval_rhs_6

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
