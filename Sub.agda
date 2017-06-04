{-# OPTIONS --cubical #-}
module Sub where

open import PathPrelude

-- "Sub {A = A} φ t" is our notation for "A[φ ↦ t]" as a type.
module _ {ℓ} {A : Set ℓ} where
  ouc-φ : {t : Partial A i1} → (s : Sub {A = A} i1 t) → (ouc s) ≡ t itIsOne
  ouc-φ s i = ouc s

  ouc-β : {φ : I} → (a : A) → ouc {φ = φ} {u = λ { _ → a }} (inc {φ = φ} a) ≡ a
  ouc-β a i = a

safeComp : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub {A = A i0} φ (u i0)
                                  → Sub {A = A i1} φ (u i1)
safeComp A φ u a0 = inc {φ = φ} (primComp A φ u (ouc a0))

safeFill : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub {A = A i0} φ (u i0) → (i : I) → A i
safeFill A φ u a0 i = ouc (safeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
       (λ j → ([ φ ↦ (u (i ∧ j)) , ~ i ↦ (λ { _ → ouc a0 })])) (inc (ouc a0)))
