{-# OPTIONS --cubical #-}
module Sub where

open import Level
open import PathPrelude

-- "Sub {A = A} φ t" is our notation for "A[φ ↦ t]" as a type.

ouc-φ : ∀ {a} {A : Set a} (let φ = i1) {t : Partial A φ} → (s : Sub {A = A} φ t) → (ouc s) ≡ t itIsOne
ouc-φ s = refl

ouc-beta : ∀ {a} {A : Set a} {φ} → (a : A) → ouc {φ = φ} {u = \ { _ → a }} (inc {φ = φ} a) ≡ a
ouc-beta a = refl


comp : ∀ {a : I → Level} (A : (i : I) → Set (a i)) (φ : I) → (u : ∀ i → Partial (A i) φ) → Sub {A = A i0} φ (u i0)
       → Sub {A = A i1} φ (u i1)
comp A φ u a0 = inc {φ = φ} (primComp A φ u (ouc a0))

safeFill : ∀ {a : I → Level} (A : (i : I) → Set (a i)) (φ : I) → (u : ∀ i → Partial (A i) φ) → Sub {A = A i0} φ (u i0) → ∀ i → A i
safeFill A φ u a0 i = ouc (comp (\ j → A (i ∧ j)) (φ ∨ ~ i) (\ j → primPOr φ (~ i) (u (i ∧ j)) \ { _ → ouc a0 }) (inc (ouc a0)))
