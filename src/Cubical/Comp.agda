module Cubical.Comp where

open import Cubical.PathPrelude hiding (fill)

open import Cubical.Sub

comp : ∀ {ℓ} → (A : (i : I) → Set ℓ) → {φ : I} →
         (u : (i : I) → Partial (A i) φ) → A i0 [ φ ↦ u i0 ]
                                         → A i1
comp A {φ} u a0 = primComp A φ u (ouc a0)

fill : ∀ {ℓ} → (A : (i : I) → Set ℓ) → (φ : I) →
         (u : (i : I) → Partial (A i) φ) → (a0 : A i0 [ φ ↦ u i0 ])
         → PathP A (ouc a0)
                   (comp A (λ { i (φ = i1) → u i _ }) a0)

fill A φ u a0 i = comp (\ j → A (i ∧ j))
                       (\ { j (φ = i1) → u (i ∧ j) itIsOne; j (i = i0) → ouc a0 })
                       (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} a0))
