{-# OPTIONS --no-termination-check #-}

module LL where

data HTerm : Set where
  true : HTerm
  false : HTerm
  _∧_ : HTerm → HTerm → HTerm
  _∨_ : HTerm → HTerm → HTerm
  _implication_ : HTerm → HTerm → HTerm

data Term : Set where
  one : Term
  zero : Term
  ⊤ : Term
  ⊥ : Term
  _⊗_ : Term → Term → Term
  _⊕_ : Term → Term → Term
  _&_ : Term → Term → Term
  ! : Term → Term
  _⊸_ : Term → Term → Term
  Nat : Term

data _⟶_ : Term → Term → Set where
  id    : ∀ {A} → A ⟶ A
  _∘_   : ∀ {A B C} → (y : B ⟶ C) → (x : A ⟶ B) → A ⟶ C
  Eone  : one ⟶ one
  _×_   : ∀ {A B C D} → (x : A ⟶ B) → (y : C ⟶ D) → (A ⊗ C) ⟶ (B ⊗ D)
  ol    : ∀ {A} → A ⟶ (one ⊗ A)
  cl    : ∀ {A} → (one ⊗ A) ⟶ A
  or    : ∀ {A} → A ⟶ (A ⊗ one)
  cr    : ∀ {A} → (A ⊗ one) ⟶ A
  ex    : ∀ {A B} → (A ⊗ B) ⟶ (B ⊗ A)
  al    : ∀ {A B C} → (A ⊗ (B ⊗ C)) ⟶ ((A ⊗ B) ⊗ C)
  ar    : ∀ {A B C} → ((A ⊗ B) ⊗ C) ⟶ (A ⊗ (B ⊗ C))
  <>    : ∀ {X} → X ⟶ ⊤
  <_,_> : ∀ {X A B} → (x : X ⟶ A) → (y : X ⟶ B) → X ⟶ (A & B)
  inl   : ∀ {A B} → A ⟶ (A ⊕ B)
  inr   : ∀ {A B} → B ⟶ (A ⊕ B)
  lcur  : ∀ {X A B} → (x : (X ⊗ A) ⟶ B) → X ⟶ (A ⊸ B)
  make  : ∀ {X A} → (x : X ⟶ A) → (y : X ⟶ one) → (z : X ⟶ (X ⊗ X)) → X ⟶ (! A)
  FST   : ∀ {A B} → (A & B) ⟶ A
  SND   : ∀ {A B} → (A & B) ⟶ B
  []    : ∀ {X} → zero ⟶ X
  [_,_] : ∀ {X A B} → (x : A ⟶ X) → (y : B ⟶ X) → (A ⊕ B) ⟶ X
  lapp  : ∀ {A B} → ((A ⊸ B) ⊗ A) ⟶ B
  read  : ∀ {A} → (! A) ⟶ A
  kill  : ∀ {A} → (! A) ⟶ one
  dupl  : ∀ {A} → (! A) ⟶ ((! A) ⊗ (! A))
  zero  : one ⟶ Nat
  succ  : Nat ⟶ Nat
  nrec  : ∀ {X} → one ⟶ X → X ⟶ X → Nat ⟶ X

data _⟶C_ : Term → Term → Set where
  <> : ∀ {X} → X ⟶C ⊤
  <_,_> : ∀ {X A B} → (x : X ⟶ A) → (y : X ⟶ B) → X ⟶C (A & B)
  inl : ∀ {A B} → A ⟶C (A ⊕ B)
  inr : ∀ {A B} → B ⟶C (A ⊕ B)
  lcur : ∀ {X A B} → (x : (X ⊗ A) ⟶ B) → X ⟶C (A ⊸ B)
  make : ∀ {X A} → (x : X ⟶ A) → (y : X ⟶ one) → (z : X ⟶ (X ⊗ X)) → X ⟶C (! A)
  zero : one ⟶C Nat
  succ : Nat ⟶C Nat

data _⟶D_ : Term → Term → Set where
  FST   : ∀ {A B} → (A & B) ⟶D A
  SND   : ∀ {A B} → (A & B) ⟶D B
  []    : ∀ {X} → zero ⟶D X
  [_,_] : ∀ {X A B} → (x : A ⟶ X) → (y : B ⟶ X) → (A ⊕ B) ⟶D X
  lapp  : ∀ {A B} → ((A ⊸ B) ⊗ A) ⟶D B
  read  : ∀ {A} → (! A) ⟶D A
  kill  : ∀ {A} → (! A) ⟶D one
  dupl  : ∀ {A} → (! A) ⟶D ((! A) ⊗ (! A))

data Value : Term → Set where
  unit : Value one
  _,_  : ∀ {A B} → Value A → Value B → Value (A ⊗ B)
  _∙_  : ∀ {A B} → (A ⟶C B) → Value A → Value B

app : {A B : Term} → (φ : A ⟶ B) → (u : Value A) → Value B
app id u = u
app (x ∘ y) u = app x (app y u)
app Eone unit = unit
app (φ × ψ) (x , y) = (app φ x , app ψ y)
app ol u = (unit , u)
app cl (unit , u) = u
app or u = (u , unit)
app cr (u , unit) = u
app ex (u , v) =  (v , u)
app al (u , (v , w)) = ((u , v) , w)
app ar ((u , v) , w) = (u , (v , w))
app <> u =  <>  ∙ u 
app < x , y > u =  < x , y > ∙ u
app FST (< φ , ψ > ∙ u) = app φ u
app SND (< φ , ψ > ∙ u) = app ψ u
app [] (() ∙ y')
app inl u =  inl ∙ u
app inr u =  inr ∙ u
app [ x , y ] (inl ∙ u) =  app x u
app [ x , y ] (inr ∙ u) =  app y u
app (lcur x) u =  (lcur x) ∙ u
app lapp ((lcur φ ∙ u) , v) =  app φ (u , v)
app (make x y z) u =  (make x y z) ∙ u
app read ((make x y z) ∙ u) = app x u
app kill ((make x y z) ∙ u) = app y u
app dupl ((make x y z) ∙ u) = app ((make x y z) × (make x y z)) (app z u)
app Eone (() ∙ y')
app (x × y) (() ∙ y0)
app cl ((() ∙ y') , y0)
app cl (() ∙ y')
app cr (y , (() ∙ y0))
app cr (() ∙ y')
app ex (() ∙ y')
app al (y , (() ∙ y0))
app al (() ∙ y')
app ar ((() ∙ y') , y0)
app ar (() ∙ y')
app lapp (() ∙ y')
app zero unit = zero ∙ unit
app zero (() ∙ y')
app succ u = succ ∙ u
app (nrec x y) (zero ∙ y1) = app x unit 
app (nrec x y) (succ ∙ y1) = app y (app (nrec x y) y1) 


hToLL : HTerm → Term
hToLL true = ⊤
hToLL false = zero
hToLL (x ∧ y) = (hToLL x) & (hToLL y)
hToLL (x ∨ y) = (! (hToLL x)) ⊕ (! (hToLL y))
hToLL (x implication y) = (! (hToLL x)) ⊸ (hToLL y)

--  ⊸

