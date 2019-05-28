module Ch03.Relations

%default total
%access public export

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

||| Dual version of the `Cons` constructor for convenience.
snoc : ReflSymmClos rel t t' -> (rel t' t'') -> ReflSymmClos rel t t''
snoc p p' = p ++ (weaken p')

||| Given a function `f` defined on relations of type `rel`, applies that to a relation in the
||| reflexive-transitive closure of `rel`
map : {func : ty -> ty} -> (f : {t1 : ty} -> {t2 : ty} -> rel t1 t2 -> rel (func t1) (func t2)) ->
      (ReflSymmClos rel t1 t2) ->
      (ReflSymmClos rel (func t1) (func t2))
map {func} f Refl = Refl
map {func} f (Cons x y) = Cons (f x) (map f y)
