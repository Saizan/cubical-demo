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

trans-id-l : ∀ {ℓ}{A : Set ℓ} {x y : A} → (p : x ≡ y) → trans (\ i → x) p ≡ p
trans-id-l {A = A} {x} {y} p i j = comp (λ _ → A)
                                             (λ { k (j = i0) → x
                                                ; k (j = i1) → p k
                                                ; k (i = i1) → p (k ∧ j) })
                                             (inc x)


trans-cong : ∀ {l l'} {A : Set l} {B : Set l'}{x y} (f : A → B)(eq : x ≡ y) z (eq' : y ≡ z)
               → trans (\ i → f (eq i)) (\ i → f (eq' i)) ≡ (\ i → f (trans eq eq' i))
trans-cong f eq = pathJ _ (trans (trans-id (λ z → f (eq z))) \ j i →  f (trans-id eq (~ j) i) )


module _ {ℓ : _} {A : Set ℓ} {a b c : A} {p : a ≡ b} {q : b ≡ c} where
    module _ {d : A} {r : c ≡ d} where
      trans-assoc : (trans p (trans q r)) ≡ trans (trans p q) r
      trans-assoc = pathJ (\ b p → (q : b ≡ c) → (trans p (trans q r)) ≡ trans (trans p q) r)
                          (\ q → trans (trans-id-l _) (cong (λ q → trans q r) (sym (trans-id-l _))))
                          b p q

module _ {ℓa ℓb : _} {A : Set ℓa} {B : Set ℓb} where
  module _ {f g : A → B} {x y : A} (H : ∀ x → f x ≡ g x) (p : x ≡ y) where
    -- Lemma 2.4.3:
    lem2-4-3 : trans (H x) (cong g p) ≡ trans (cong f p) (H y)
    lem2-4-3 = pathJ (λ y p → trans (H x) (cong g p) ≡ trans (cong f p) (H y))
                     (trans (trans-id (H x)) (sym (trans-id-l (H x)))) y p
