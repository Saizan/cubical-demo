{-# OPTIONS --cubical --postfix-projections #-}
module Cubical.IsoToEquiv where

open import Cubical hiding (fill)
open import Cubical.Comp
open import Cubical.FromStdLib
open import Cubical.NType.Properties

Square : ∀ {ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A}
          (u : a0 ≡ a1) (v : b0 ≡ b1) (r0 : a0 ≡ b0) (r1 : a1 ≡ b1) → Set ℓ
Square {A = A} u v r0 r1 = PathP (λ i → (u i ≡ v i)) r0 r1

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
         (s : (y : B) → (f (g y)) ≡ y) (t : (x : A) → (g (f x)) ≡ x) where

  private
    module _ (y : B) (x0 x1 : A) (p0 : y ≡ (f x0)) (p1 : y ≡ (f x1)) where

      fill0 : ∀ (_ _ : I) → A
      fill0 i j = fill (λ _ → A) _ (λ k → λ { (i = i1) → t x0 k
                                            ; (i = i0) → g y })
                                   (inc (g (p0 i))) j

      fill1 : ∀ (_ _ : I) → A
      fill1 i j = fill (λ _ → A) _ (λ k → λ { (i = i1) → t x1 k
                                            ; (i = i0) → g y })
                                   (inc (g (p1 i))) j

      fill2 : ∀ (_ _ : I) → A
      fill2 i j = fill (λ _ → A) _ (λ k → λ { (i = i1) → fill1 k i1
                                            ; (i = i0) → fill0 k i1 })
                                   (inc (g y)) j
      p : x0 ≡ x1
      p i = fill2 i i1

      sq  : ∀ (_ _ : I) → A
      sq i j = comp (λ _ → A) (λ k → λ { (i = i1) → fill1 j (~ k)
                                       ; (i = i0) → fill0 j (~ k)
                                       ; (j = i1) → t (fill2 i i1) (~ k)
                                       ; (j = i0) → g y })
                              (inc (fill2 i j))

      sq1 : Square {A = B} (λ _ → y) (λ i → f (p i)) p0 p1
      sq1 i j = comp (λ _ → B) (λ k → λ { (i = i1) → s (p1 j) k
                                        ; (i = i0) → s (p0 j) k
                                        ; (j = i1) → s (f (p i)) k
                                        ; (j = i0) → s y k })
                               (inc (f (sq i j)))

      lemIso : _≡_ {A = fiber f y} (x0 , p0) (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = sq1 i

  isoToEquiv : isEquiv A B f
  isoToEquiv .equiv-proof y .fst .fst = g y
  isoToEquiv .equiv-proof y .fst .snd i = s y (~ i)
  isoToEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (λ i → s y (~ i)) (snd z)


module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (w : A ≃ B) where
  invEq : (y : B) → A
  invEq y = fst (fst (snd w .equiv-proof y))

  secEq : (x : A) → invEq (fst w x) ≡ x
  secEq x = λ i → fst (snd (snd w .equiv-proof (fst w x)) (x , (λ j → fst w x)) i)

  retEq : (y : B) → fst w (invEq y) ≡ y
  retEq y = λ i → snd (fst (snd w .equiv-proof y)) (~ i)

isoToPath : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (g : B → A)
  (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) → A ≡ B
isoToPath f g s t = equivToPath (_ , isoToEquiv f g s t)

invEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
invEquiv {A} {B} f = invEq f , isoToEquiv (invEq f) (fst f) (secEq f) (retEq f)

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
  invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
  invEquivInvol f i .fst = fst f
  invEquivInvol f i .snd = propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i
