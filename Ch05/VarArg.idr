module Ch05.VarArg

import Data.Vect

--------------------------------------------------------------------------------
-- Auxillary stuff for defining functions with a variable # of args
--------------------------------------------------------------------------------

||| Type of vectors of fixed length of elements of varying types
data VarVect : (n : Nat) -> Vect n Type -> Type where
  VarNil : VarVect Z []
  VarCons : (a : Type) ->
            (x : a) ->
            VarVect n as ->
            VarVect (S n) (a :: as)

VarArgType : (numArgs : Nat) ->
             Vect numArgs Type ->
             Type
VarArgType Z [] = ?VarArgType_rhs_1
VarArgType (S k) (a :: as) = a -> VarArgType k as



-- Suppose we want to define a function
--
--     f : a_1 -> a_2 -> ... -> a_n -> b
-- 
-- for some [a_1, ..., a_n] : Vect n Type. Then there are two ways to do that:
--
-- One: Starting from the knowledge of
--
--     \x1, ... x(n-1) => f x1 ... x(n-1) xn
--
-- for arbitrary but fixed `xn`, we define `f`.
