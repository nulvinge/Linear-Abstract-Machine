module Testing where

open import LL
open import LAM

test : ∀ {A B} → (Value ((A & B) ⊸ A))
test = (lcur (FST ∘ cl)) ∙ unit

test2 : ∀ {A B} → (one ⟶ ((A & B) ⊸ A))
test2 = lcur (FST ∘ cl)

test2R : ∀ {A B} → Value ((A & B) ⊸ A)
test2R {A} {B} = run (linear (test2 {A} {B})) unit []

test3 : ∀ {A B} → ((A & B) ⟶ A)
test3 {A} {B} = lapp ∘ (or ∘ lcur (FST ∘ cr))

test3R : Value one
test3R = run (linear (test3 ∘ < id , id >)) unit []

add : (Nat ⊗ Nat) ⟶ Nat
add = lapp ∘ ((nrec (lcur cl) (lcur (succ ∘ lapp))) × id)

ZERO = zero ∙ unit
ONE = succ ∙ ZERO
TWO = succ ∙ ONE

testAdd1 : Value Nat
testAdd1 = app add (ONE , TWO)

testAdd2 : Value Nat
testAdd2 = run (linear add) (ONE , TWO) []

test4 : ∀ {A B} → ((A & B) ⊗ (A & B)) ⟶ (A ⊗ B)
test4 = FST × SND

test4R : Value (Nat ⊗ Nat)
test4R = app test4 ((< zero , succ ∘ zero > ∙ unit) , ((< zero , succ ∘ zero > ∙ unit)))

test5 : ∀ {A B C} → ((A & B) ⊗ (B ⊸ C)) ⟶ ((A ⊗ (B ⊸ C)) & C)
test5 = < FST × id , lapp ∘ (ex ∘ (SND × id)) >

test5R : Value ((one ⊗ (Nat ⊸ Nat)) & Nat)
test5R = app test5 ((< id , zero > ∙ unit) , ((lcur (succ ∘ cl)) ∙ unit) )

test6 : ∀ {A B C D} → ((A & B) ⊗ (C & D)) ⟶ ((A ⊗ C) & (B ⊗ D))
test6 = < FST × FST , SND × SND >

test7 : ∀ {A B} → (A & B) ⟶ (B & A)
test7 = < SND , FST >

test8 : ∀ {A B} → (A ⊕ B) ⟶ (B ⊕ A)
test8 = [ inr , inl ]

test11 : ∀ {A B C} → ((A ⊸ B) ⊗ (B ⊸ C)) ⟶ (A ⊸ C)
test11 = lcur ((((lapp ∘ ex) ∘ ((lapp ∘ ex) × id)) ∘ al) ∘ ex)

test12 : ∀ {A B C} → ((A ⊗ B) ⊸ C) ⟶ (A ⊸ (B ⊸ C))
test12 = lcur (lcur (lapp ∘ ar))

test13 : ∀ {A B C} → ((A ⊗ A) ⊗ ((A ⊸ B) ⊗ (A ⊸ C))) ⟶ (B ⊗ C)
test13 = ((lapp ∘ ex) × lapp) ∘ (((ar ∘ (al × id)) ∘ ex) ∘ ar)

test14 : (Nat ⊗ Nat) ⟶ (Nat ⊗ Nat)
test14 = (succ × (succ ∘ succ))

test14R : Value (Nat ⊗ Nat)
test14R = run (linear test14) (ZERO , ZERO) []

bnot : ∀ {A B} → (A ⊕ B) ⟶ (B ⊕ A)
bnot = [ inr , inl ]

band : ((one ⊕ one) ⊕ (one ⊕ one)) ⟶ (one ⊕ one)
band = [ [ inl , inl ] , id ]

bor : ((one ⊕ one) ⊕ (one ⊕ one)) ⟶ (one ⊕ one)
bor = [ id , [ inr , inr ] ]

bxor : ((one ⊕ one) ⊕ (one ⊕ one)) ⟶ (one ⊕ one)
bxor = [ id , bnot ]

truefalse : Value ((one ⊕ one) ⊕ (one ⊕ one))
truefalse = inr ∙ (inl ∙ unit)

xorR : Value (one ⊕ one)
xorR = run (linear bxor) truefalse []

orR : Value (one ⊕ one)
orR = run (linear bor) truefalse []

andR : Value (one ⊕ one)
andR = run (linear band) truefalse []

plusdist : ∀ {A} → (A ⊗ (one ⊕ one)) ⟶ ((A ⊗ one) ⊕ (A ⊗ one))
plusdist = inl ∘ (id × [ id , id ])

boolinv : ((one ⊕ one) ⊕ (one ⊕ one)) ⟶ ((one ⊕ one) ⊗ (one ⊕ one))
boolinv = [ [ (inl × inl) ∘ ol , (inl × inr) ∘ ol ] , [ (inr × inl) ∘ ol , (inr × inr) ∘ ol ] ]

true2 : ∀ {A B} → Value ((A & B) ⊸ (A ⊕ B))
true2 = (lcur ((inl ∘ FST) ∘ cl)) ∙ unit

false2 : ∀ {A B} → Value ((A & B) ⊸ (A ⊕ B))
false2 = (lcur ((inr ∘ SND) ∘ cl)) ∙ unit

