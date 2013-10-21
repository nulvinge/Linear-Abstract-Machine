{-# OPTIONS --no-termination-check #-}

module LAM where

open import LL
open import List

data Dump : List Term → Set where
  [] : Dump []
  _∷_ : ∀ {D} → {A : Term} → Value A → Dump D → Dump (A :: D)

data A* (A : Term → Term → List Term → List Term → Set) : Term → Term → List Term → List Term → Set where
  []  : ∀ {a d} → A* A a a d d
  _∷_ : ∀ {a b c d e f} → (A a b d e) → (A* A b c e f) → (A* A a c d f)

_+_ : ∀ {A a b c d e f} → (A* A a b d e) → (A* A b c e f) → (A* A a c d f)
[]       + ys = ys
(x ∷ xs) + ys = x ∷ (xs + ys)

data Instruction : Term → Term → List Term → List Term → Set where
  pushl  : ∀ {D U V} → Instruction (U ⊗ V) U D (V :: D)
  consl  : ∀ {D U V} → Instruction U (U ⊗ V) (V :: D) D
  pushr  : ∀ {D U V} → Instruction (U ⊗ V) V D (U :: D)
  consr  : ∀ {D U V} → Instruction V (U ⊗ V) (U :: D) D
  ol     : ∀ {D U} → Instruction U (one ⊗ U) D D
  cl     : ∀ {D U} → Instruction (one ⊗ U) U D D
  or     : ∀ {D U} → Instruction U (U ⊗ one) D D
  cr     : ∀ {D U} → Instruction (U ⊗ one) U D D
  ex     : ∀ {D U V} → Instruction (U ⊗ V) (V ⊗ U) D D
  al     : ∀ {D A B C} → Instruction (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C) D D
  ar     : ∀ {D A B C} → Instruction ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) D D
  constr : ∀ {A B D} → A ⟶C B → Instruction A B D D
  FST    : ∀ {D U V} → Instruction (U & V) U D D
  SND    : ∀ {D U V} → Instruction (U & V) V D D
  altv   : ∀ {D A B X} → A* Instruction A X D D → A* Instruction B X D D → Instruction (A ⊕ B) X D D
  lapp   : ∀ {D A B} → Instruction ((A ⊸ B) ⊗ A) B D D
  []     : ∀ {D X} → Instruction zero X D D
  read   : ∀ {D X} → Instruction (! X) X D D
  kill   : ∀ {D X} → Instruction (! X) one D D
  dupl   : ∀ {D X} → Instruction (! X) ((! X) ⊗ (! X)) D D
--  empty : Instruction
  nrec   : ∀ {D X} → A* Instruction one X D D → A* Instruction X X D D → Instruction Nat X D D

list : ∀ {A a b d e} → A a b d e → A* A a b d e
list a = a ∷ []

linear : ∀ {A B D} → A ⟶ B → A* Instruction A B D D
linear id = []
linear (y ∘ x) = (linear x + linear y)
linear Eone = []
linear (x × y) = pushl
               ∷ (linear x
               + (consl
               ∷ (pushr
               ∷ (linear y
               + (consr
               ∷ [])))))
linear ol = list ol
linear cl = list cl
linear or = list or
linear cr = list cr
linear ex = list ex
linear al = list al
linear ar = list ar
--linear {A} {⊤} D <> = ins D (list (constr {A} {⊤} <>))
linear <> = list (constr <>)
linear < x , y > = list (constr < x , y >)
linear FST = list FST
linear SND = list SND
linear [] = list []
linear {A} {.A ⊕ B} inl = list (constr {A} {A ⊕ B} inl)
linear {B} {A ⊕ .B} inr = list (constr {B} {A ⊕ B} inr)
linear [ x , y ] = list (altv (linear x) (linear y))
linear (lcur x) =  list (constr (lcur x))
linear lapp = list lapp
linear (make x y z) =  list (constr (make x y z))
linear read = list read
linear kill = list kill
linear dupl = list dupl
linear zero = list (constr zero)
linear succ = list (constr succ)
linear (nrec x y) = list (nrec (linear x) (linear y))

run : ∀ {A B D E} → A* Instruction A B D E → Value A → Dump D → Value B
run (pushl ∷ C) (u , v) D = run C u (v ∷ D)
run (consl ∷ C) u (v ∷ D) = run C (u , v)  D
run (pushr ∷ C) (u , v) D = run C v (u ∷ D)
run (consr ∷ C) v (u ∷ D) = run C (u , v) D
run (ol ∷ C) u D = run C (unit , u) D
run (cl ∷ C) (unit , u) D = run C u D
run (or ∷ C) u D = run C (u , unit) D
run (cr ∷ C) (u , unit) D = run C u D
run (ex ∷ C) (u , v) D = run C (v , u) D
run (al ∷ C) (u , (v , w)) D = run C ((u , v) , w) D
run (ar ∷ C) ((u , v) , w) D = run C (u , (v , w)) D
run (constr γ ∷ C) u D = run C (γ ∙ u) D
run (FST ∷ C) (< C' , C'' > ∙ u) D = run (linear C' + C) u D
run (SND ∷ C) (< C' , C'' > ∙ u) D = run (linear C'' + C) u D
--  altv   : ∀ {D E F A B X} → (A* Instruction A X D E) → (A* Instruction B X D F) → Instruction (A ⊕ B) X D D
run (altv C' C'' ∷ C) (inl ∙ u) D = run (C' + C)  u D
run (altv C' C'' ∷ C) (inr ∙ u) D = run (C'' + C) u D
run (lapp ∷ C) (((lcur C') ∙ u) , v) D = run (linear C' + C) (u , v) D
run (read ∷ C) (make x y z ∙ u) D = run ((linear x) + C) u D
run (kill ∷ C) (make x y z ∙ u) D = run ((linear y) + C) u D
run (dupl ∷ C) (make x y z ∙ u) D = run ((linear z + linear ((make x y z) × (make x y z))) + C) u D
run (nrec x y ∷ C) (zero ∙ y0) D = run (x + C) unit D
run (nrec x y ∷ C) (succ ∙ n) D = run ((nrec x y ∷ y) + C) n D
run [] u [] = u
run [] u (D' ∷ D) = u --this is wrong, D should be empty
--these are empty. Should be possible to prove this by extending Instruciton
run (pushl ∷ C) (() ∙ y0) D
run (pushr ∷ C) (() ∙ y') D
run (cl ∷ C) ((() ∙ y') , y0) D
run (cl ∷ C) (() ∙ y') D
run (cr ∷ C) (y0 , (() ∙ y')) D
run (cr ∷ C) (() ∙ y') D
run (ex ∷ C) (() ∙ y') D
run (al ∷ C') (y , (() ∙ y0)) D
run (al ∷ C') (() ∙ y') D
run (ar ∷ C') ((() ∙ y') , y) D
run (ar ∷ C') (() ∙ y') D
run (lapp ∷ C) (() ∙ y') D 
run ([] ∷ C) (() ∙ y') D

