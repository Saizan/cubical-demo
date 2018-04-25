{-# OPTIONS --cubical #-}
module Cubical.Quotient where


open import Cubical.PushOut
open import Cubical.FromStdLib
open import Cubical.PathPrelude
open import Cubical.Lemmas

module M {l} (A : Set l) (R : A → A → Set l) (R-refl : ∀ x → R x x) where

  Quot = P {A = A} {B = A} {C = Σ A \ x → Σ A \ y → R x y} (\ z → z .fst) \ x → x .snd .fst

  quot : A → Quot
  quot = inl

  quot-path : ∀ {x y} → R x y → quot x ≡ quot y
  quot-path r = trans (push (_ , _ , r)) (sym (push (_ , _ , R-refl _)))

  open import Cubical.Comp

  quot-elim' : ∀ {p} (P : Quot → Set p) (f : (x : A) → P (quot x)) →
                (∀ x y → (r : R x y) → PathP (\ i → P (push (_ , _ , r) i))
                     (f x) (transp (\ i → P (push (_ , _ , R-refl y) i)) (f y)))
                → ∀ x → P x
  quot-elim' P f [f] = primPushOutElim P f (\ b → transp (\ i → P (push (_ , _ , R-refl b) i)) (f b))
                                      \ { (x , y , r) → [f] x y r }







  lemma : ∀ {l} {A B C : Set l}
        (p : Path B C) (q : Path A C) {x : B} {y : A}
          → PathP (\ i → trans p (sym q) i) x y → PathP (\ i → p i) x (transp (\ i → q i) y)
  lemma {l} {A} {B} p q = pathJ (\ C q → (p : Path B C) {x : B} {y : A}
          → PathP (\ i → trans p (sym q) i) x y → PathP (\ i → p i) x (transp (\ i → q i) y))
                  (\ p {x} {y} eq → transp (\ i → PathP (\ j → trans-id p i j) x (sym (transp-refl y) i)) eq) _ q p


  module _ {p} (P : Quot → Set p) (f : (x : A) → P (quot x))
                ([f] : ∀ x y → (r : R x y) → PathP (\ i → P (quot-path r i)) (f x) (f y))
                where
    quot-elim-path-lem : (c : Σ A (λ x → Σ A (R x))) → PathP (λ i → P (push c i)) (f (c .fst))
                        (transp
                     (λ i →
                        P (push (c .snd .fst , c .snd .fst , R-refl (c .snd .fst)) i))
                        (f (c .snd .fst)))

    quot-elim-path-lem (x , y , r) i = lemma (λ z → P (push (x , y , r) z)) (λ z → P (push (y , y , R-refl y) z))
                    (transp (\ i → PathP (\ j → trans-cong P (push (x , y , r))
                                         (inl y) (sym (push (y , y , R-refl y)))
                            (~ i) j) (f x) (f y)) ([f] x y r)) i


    quot-elim : ∀ x → P x
    quot-elim = quot-elim' P f λ x y r → quot-elim-path-lem (x , y , r)
