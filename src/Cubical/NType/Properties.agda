{-# OPTIONS --cubical #-}
module Cubical.NType.Properties where

open import Cubical.PathPrelude
open import Cubical.Prelude

lemProp : ∀ {ℓ} {A : Set ℓ} → (A → isProp A) → isProp A
lemProp h = λ a → h a a

module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where
  -- Π preserves propositionality in the following sense:
  propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
  propPi h f0 f1  = λ i → λ x → (h x (f0 x) (f1 x)) i

  -- `lemPropF` can be used to prove equalities in the dependent function space
  -- of propositions.
  lemPropF : (P : (x : A) → isProp (B x)) {a0 a1 : A}
    (p : a0 ≡ a1) {b0 : B a0} {b1 : B a1} → PathP (λ i → B (p i)) b0 b1
  lemPropF P p {b0} {b1} = λ i → P (p i)
     (primComp (λ j → B (p (i ∧ j)) ) (~ i) (λ _ →  λ { (i = i0) → b0 }) b0)
     (primComp (λ j → B (p (i ∨ ~ j)) ) (i) (λ _ → λ{ (i = i1) → b1 }) b1) i

  lemSig : (pB : (x : A) → isProp (B x))
    (u v : Σ A B) (p : fst u ≡ fst v) → u ≡ v
  lemSig pB u v p = λ i → (p i) , ((lemPropF pB p) {snd u} {snd v} i)

  propSig : (pA : isProp A) (pB : (x : A) → isProp (B x)) → isProp (Σ A B)
  propSig pA pB t u = lemSig pB t u (pA (fst t) (fst u))

module _ {ℓ} {A : Set ℓ} where
  propSet : isProp A → isSet A
  propSet h = λ(a b : A) (p q : a ≡ b) j i →
    primComp (λ k → A)((~ i ∨ i) ∨ (~ j ∨ j))
      (λ k → λ { (i = i0) → h a a k; (i = i1) → h a b k
               ; (j = i0) → h a (p i) k; (j = i1) → h a (q i) k }) a

  propIsContr : isProp (isContr A)
  propIsContr = lemProp (λ t → propSig (λ a b → trans (sym (snd t a)) (snd t b))
         (λ x → propPi (propSet ((λ a b → trans (sym (snd t a)) (snd t b))) x)))

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
  propIsEquiv : (f : A → B) → isProp (isEquiv A B f)
  propIsEquiv f = λ u0 u1 → λ i → λ y → propIsContr (u0 y) (u1 y) i
