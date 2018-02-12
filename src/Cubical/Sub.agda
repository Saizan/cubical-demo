{-# OPTIONS --cubical #-}
module Cubical.Sub where

open import Cubical
open import Cubical.Prelude

-- "Sub A φ t" is another notation for "A[φ ↦ t]" as a type.

module _ {ℓ} {A : Set ℓ} where
  ouc-φ : {t : Partial A i1} → (s : A [ i1 ↦ t ]) → (ouc s) ≡ t itIsOne
  ouc-φ s i = ouc s

  ouc-β : {φ : I} → (a : A)
          → ouc {φ = φ} {u = λ { (φ = i1) → a }} (inc {φ = φ} a) ≡ a
  ouc-β a i = a


Comp : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
       (u : (i : I) → Partial (A i) φ) → A i0 [ φ ↦ u i0 ]
                                       → A i1
Comp A φ u a0 = primComp A φ u (ouc a0)


Fill : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
       (u : (i : I) → Partial (A i) φ) → A i0 [ φ ↦ u i0 ]
                                       → (i : I) → A i
Fill A φ u a0 i = Comp (\ j → A (i ∧ j)) _ (\ { j (φ = i1) → u (i ∧ j) itIsOne
                                              ; j (i = i0) → ouc a0
                                              })
                                           (inc (ouc a0))











safeComp : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub (A i0) φ (u i0)
                                  → Sub (A i1) φ (u i1)
safeComp A φ u a0 = inc {φ = φ} (primComp A φ u (ouc a0))


safeFill : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub (A i0) φ (u i0) → (i : I) → A i
safeFill A φ u a0 i = ouc (safeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
       (λ j → ([ φ ↦ (u (i ∧ j)) , ~ i ↦ (λ { (i = i0) → ouc a0 })])) (inc (ouc a0)))
