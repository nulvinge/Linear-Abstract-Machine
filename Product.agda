module Product where

-- cf Pierce, figure 11-5 p 126

data _×_ (A B : Set) : Set where
  <_,_> : A -> B -> A × B

-- Pierce uses {_,_}

fst : {A B : Set} -> A × B -> A
fst < a , b > = a

-- Pierce uses t.1 for fst t, the "first projection"

snd : {A B : Set} -> A × B -> B
snd < a , b > = b

-- Pierce uses t.2 for snd t, the "second projection"

-- Pierce's evaluation rules are for "strict" pairs, evaluating the first component to a value, then the second component. When projections are computed we first compute both components of the pair, then throw one away

-- In general we can have tuples (pairs, triples, quadruples, ...)
