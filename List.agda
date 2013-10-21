module List where

open import Product

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

-- yields polymorphic datatype
-- List : Set -> Set
-- [] : {A : Set} -> List A
-- _::_ : {A : Set} -> A -> List A -> List A

-- head is a partial functions in Haskell,
-- it is not defined on the empty list

head : {A : Set} → (a : A) -> List A -> A
head a []         = a
head a (a' :: as) = a'

tail : {A : Set}-> List A -> List A
tail []        = []
tail (_ :: xs) = xs

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

zip : {A B : Set} -> List A -> List B -> List (A × B)
zip []        []        = []
zip (x :: xs) (y :: ys) = < x , y > :: zip xs ys
zip _         _         = []

_++_ : ∀ {A} → List A → List A → List A
[]       ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- the intention is to "zip" lists of the same length, the last clause will
-- only be used when lists are of different lengths  
