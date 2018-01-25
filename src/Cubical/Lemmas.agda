{-# OPTIONS --cubical #-}
module Cubical.Lemmas where

open import Cubical.PathPrelude
open import Cubical.Comp


trans-id : ∀ {ℓ}{A : Set ℓ} {x y : A} → (p : x ≡ y) → trans p (\ i → y) ≡ p
trans-id {A = A} {x} {y} p i j = Cubical.Comp.fill (λ _ → A) _
                                             (λ { i (j = i0) → x
                                                ; i (j = i1) → y })
                                             (inc (p j))
                                             (~ i)

trans-cong : ∀ {l l'} {A : Set l} {B : Set l'}{x y} (f : A → B)(eq : x ≡ y) z (eq' : y ≡ z)
               → trans (\ i → f (eq i)) (\ i → f (eq' i)) ≡ (\ i → f (trans eq eq' i))
trans-cong f eq = pathJ _ (trans (trans-id (λ z → f (eq z))) \ j i →  f (trans-id eq (~ j) i) )
