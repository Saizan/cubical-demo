{-# OPTIONS --cubical #-}
module Sub where

open import Level
open import Cube


ouc-φ : ∀ {a} {A : Set a} (let φ = i1) {t : Partial A φ} → (s : Sub φ t) → (ouc s) ≡ t itIsOne
ouc-φ s = refl

ouc-beta : ∀ {a} {A : Set a} {φ} → (a : A) → ouc {φ = φ} {u = \ { _ → a }} (inc {φ = φ} a) ≡ a
ouc-beta a = refl


comp : ∀ {a : I → Level} (A : (i : I) → Set (a i)) (φ : I) → (u : ∀ i → Partial (A i) φ) → Sub {A = A i0} φ (u i0) → Sub {A = A i1} φ (u i1)
comp A φ u a0 = inc {φ = φ} (primComp A φ u (ouc a0))
