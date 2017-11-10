{-# OPTIONS --cubical #-}
module Cubical.AIM_Demo.DemoUniv where

open import Cubical.PathPrelude renaming (equivToPath to ua)
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.List
open import Cubical.NotIsEquiv using (notIsEquiv)

notEquiv : Bool ≃ Bool
notEquiv = not , notIsEquiv

notpath : Path Bool Bool
notpath = ua {A = Bool} {B = Bool} notEquiv

test : Bool
test = primComp (\ i → ua {A = Bool} {B = Bool} notEquiv i)
                i0 (\ _ → empty) true

test-is-false : test ≡ false
test-is-false = refl


ListNot : List Bool ≡ List Bool
ListNot = \ i → List (notpath i)

emptyL : List Bool
emptyL = primComp (\ _ → List Bool) i0 (\ _ → empty) []

empty∷ : List Bool
empty∷ = primComp (\ _ → List Bool) i0 (\ _ → empty) (true ∷ [])

trues : List Bool
trues = true ∷ true ∷ []

falses : List Bool
falses = primComp (\ i → ListNot i) i0 (\ _ → empty) trues

test-falses : falses ≡ false ∷ false ∷ []
test-falses = refl

trues2 : List Bool
trues2 = primComp (\ i → trans ListNot ListNot i) i0 (\ _ → empty) trues

test-trues2 : trues2 ≡ true ∷ true ∷ []
test-trues2 = refl

trues3 : List Bool
trues3 = primComp (\ i → let p = trans ListNot ListNot in
                         trans p p i)
                  i0
                  (\ _ → empty)
                  trues


test-trues3 : trues3 ≡ true ∷ true ∷ []
test-trues3 = refl
