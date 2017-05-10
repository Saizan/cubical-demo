{-# OPTIONS --cubical -vtc.data.proj:20 #-}
open import PathPrelude
open import Data.Bool
open import Data.Product
open import Univalence
-- open import Data.List
open import NotIsEquiv using (notIsEquiv)

notEquiv : Equiv Bool Bool
notEquiv = not , notIsEquiv

notpath : Path Bool Bool
notpath = ua {A = Bool} {B = Bool} notEquiv

test : Bool
test = primComp (\ i → ua {A = Bool} {B = Bool} notEquiv i)
                i0 (\ _ → empty) true

test-is-false : test ≡ false
test-is-false = refl



data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) → List A → List A

infixr 20 _∷_

data Tr (A : Set) : Set where
  zero : Tr A
  suc : Tr A → Tr A → Tr A

ListNot : List Bool ≡ List Bool
ListNot = \ i → List (notpath i)

emptyL : List Bool
emptyL = primComp (\ _ → List Bool) i0 (\ _ → empty) []

empty∷ : List Bool
empty∷ = primComp (\ _ → List Bool) i0 (\ _ → empty) (true ∷ [])

one : Tr Bool
one = primComp (\ _ → Tr Bool) i0 (\ _ → empty) (suc zero zero)

trues : List Bool
trues = true ∷ true ∷ []

falses : List Bool
falses = primComp (\ i → ListNot i) i0 (\ _ → empty) trues

trues2 : List Bool
trues2 = primComp (\ i → trans ListNot ListNot i) i0 (\ _ → empty) trues

trues3 : List Bool
trues3 = primComp (\ i → let p = trans ListNot ListNot in
                         trans p p i)
                  i0
                  (\ _ → empty)
                  trues
