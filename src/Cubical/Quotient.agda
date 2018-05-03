{-# OPTIONS --cubical --caching #-}
module Cubical.Quotient where


open import Cubical.PushOut
open import Cubical.FromStdLib
open import Cubical.PathPrelude
open import Cubical.Lemmas
open import Cubical.CoEqualizer

module TheQuot {l} (A : Set l) (R : A → A → Set l) (R-refl : ∀ x → R x x) where

  module QQ = TheCoEq (Σ A \ x → Σ A \ y → R x y) A (\ z → z .fst) (\ x → x .snd .fst)
  open QQ renaming (CoEq to Quot; coeq to quot)

  quot-path : ∀ {x y} → R x y → quot x ≡ quot y
  quot-path r = coeq-path (_ , _ , r)

  module _ {p} (P : Quot → Set p) (f : (x : A) → P (quot x))
                ([f] : ∀ x y → (r : R x y) → PathP (\ i → P (quot-path r i)) (f x) (f y))
                where

    quot-elim : ∀ x → P x
    quot-elim = Elim.coeq-elim {C = P} f (\ { (x , y , r) → [f] x y r })


    quot-elim-path : ∀ x y (r : R x y) → (\ i → quot-elim (quot-path r i)) ≡ [f] x y r
    quot-elim-path x y r = Elim.coeq-elim-path {C = P} f ((\ { (x , y , r) → [f] x y r })) (x , y , r)
