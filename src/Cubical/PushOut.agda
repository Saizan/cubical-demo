{-# OPTIONS --cubical #-}
module Cubical.PushOut where

open import Cubical.PathPrelude
open import Cubical.Sub
open import Cubical.Prelude

postulate
  P : ∀ {l} → {A B C : Set l} → (f : C → A) (g : C → B) → Set l
  inl : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → A → P f g
  inr : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → B → P f g
  push : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → (c : C) → inl {C = C} {f} {g} (f c) ≡ inr (g c)

{-# BUILTIN PUSHOUT P #-}
{-# BUILTIN PUSHOUTINL inl #-}
{-# BUILTIN PUSHOUTINR inr #-}
{-# BUILTIN PUSHOUTPUSH push #-}


primitive
  primPushOutHComp : ∀ {l} → {A B C : Set l} → {f : C → A} {g : C → B} → (φ : I) → (u : (i : I) → Partial (P f g) φ) → Sub {l} (P f g) φ (u i0) → P f g
  primPushOutForward : ∀ {l : I → Level} → {A B C : (i : I) → Set (l i)} → {f : ∀ i → C i → A i} {g : ∀ i → C i → B i} →
                    (r : I) → (u : P (f r) (g r)) → P (f i1) (g i1)
  primPushOutElim : ∀ {l m} → {A B C : Set l} → {f : C → A} {g : C → B} → (M : P f g -> Set m)
                    → (il : ∀ a → M (inl a)) (ir : ∀ b → M (inr b))
                    → (p : ∀ c → PathP (\ i → M (push c i)) (il (f c)) (ir (g c)))
                    → ∀ x → M x
