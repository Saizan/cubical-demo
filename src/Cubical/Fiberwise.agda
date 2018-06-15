{-# OPTIONS --cubical #-}
module Cubical.Fiberwise where

open import Cubical.PathPrelude
open import Cubical.FromStdLib
open import Cubical.NType
open import Cubical.NType.Properties
open import Cubical.Lemmas
open import Cubical.GradLemma
open import Cubical.Sigma

module _ {a p q} {A : Set a} (P : A → Set p) (Q : A → Set q)
         (f : ∀ x → P x → Q x)
         where
  private
    total : (Σ A P) → (Σ A Q)
    total = (\ p → p .fst , f (p .fst) (p .snd))

  -- Thm 4.7.6
  fibers-total : ∀ {xv} → fiber total (xv) ≃ fiber (f (xv .fst)) (xv .snd)
  fibers-total {xv} = h , gradLemma h g h-g g-h
   where
    h : ∀ {xv} → fiber total (xv) → fiber (f (xv .fst)) (xv .snd)
    h {xv} (p , eq) = pathJ (\ xv eq → fiber (f (xv .fst)) (xv .snd)) ((p .snd) , refl) xv (sym eq)
    g : ∀ {xv} → fiber (f (xv .fst)) (xv .snd) → fiber total xv
    g {xv} (p , eq) = ((xv .fst) , p) , (\ i → _ , eq i)
    h-g : ∀ {xv} y → h {xv} (g {xv} y) ≡ y
    h-g {x , v} (p , eq) = pathJ (λ _ eq₁ → h (g (p , sym eq₁)) ≡ (p , sym eq₁)) (pathJprop (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) ((p , refl))) v (sym eq)
    g-h : ∀ {xv} y → g {xv} (h {xv} y) ≡ y
    g-h {xv} ((a , p) , eq) = pathJ (λ _ eq₁ → g (h ((a , p) , sym eq₁)) ≡ ((a , p) , sym eq₁)) ((cong g (pathJprop (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) (p , refl)))
                                    )
                                (xv .fst , xv .snd) (sym eq)
  -- half of Thm 4.7.7
  fiberEquiv : ([tf] : isEquiv (Σ A P) (Σ A Q) total)
               → ∀ x → isEquiv (P x) (Q x) (f x)
  fiberEquiv [tf] x .equiv-proof y = equivPreservesNType {n = ⟨-2⟩} fibers-total ([tf] .equiv-proof (x , y))


module ContrToUniv {ℓ : Level} {U : Set ℓ} {ℓr} (_~_ : U → U → Set ℓr)
       (idTo~ : ∀ {A B} → A ≡ B → A ~ B )
       (c : ∀ A → isContr (Σ U \ X → A ~ X))
       where

  lemma : ∀ {A B} → isEquiv _ _ (idTo~ {A} {B})
  lemma {A} {B} = fiberEquiv (λ z → A ≡ z) (λ z → A ~ z) (\ B → idTo~ {A} {B})
                  (λ { .equiv-proof y → sigPresContr ((_ , refl) , (\ z → contrSingl (z .snd)))
                                      \ a → hasLevelPath ⟨-2⟩ (HasLevel+1 ⟨-2⟩ (c A)) _ _ })
                  B
