{-# OPTIONS --cubical --postfix-projections #-}
module Cubical.GradLemma where

open import Cubical
open import Cubical.FromStdLib
open import Cubical.NType.Properties

Square : ∀ {ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A}
          (u : a0 ≡ a1) (v : b0 ≡ b1) (r0 : a0 ≡ b0) (r1 : a1 ≡ b1) → Set ℓ
Square {A = A} u v r0 r1 = PathP (λ i → (u i ≡ v i)) r0 r1

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
         (s : (y : B) → (f (g y)) ≡ y) (t : (x : A) → (g (f x)) ≡ x) where

  private
    module _ (y : B) (x0 x1 : A) (p0 : y ≡ (f x0)) (p1 : y ≡ (f x1)) where
    
      rem0 : g y ≡ x0
      rem0 = λ i → primComp (λ _ → A) _ (λ k → λ { (i = i1) → t x0 k
                                                 ; (i = i0) → g y }) (g (p0 i))
      rem1 : g y ≡ x1
      rem1 = λ i → primComp (λ _ → A) _ (λ k → λ { (i = i1) → t x1 k
                                                 ; (i = i0) → g y})  (g (p1 i))
  
      p    : x0 ≡ x1
      p    = λ i → primComp (λ _ → A) _ (λ k → λ { (i = i1) → rem1 k
                                                 ; (i = i0) → rem0 k })  (g y)
  
      fill0 : Square (λ i → g (p0 i)) rem0 (λ i → g y) (t x0)
      fill0 i j = primComp (λ _ → A) _ (λ k → λ { (i = i1) → t x0 (j ∧ k)
                                                ; (i = i0) → g y
                                                ; (j = i0) → g (p0 i) })
                                   (g (p0 i))
  
      fill1 : Square (λ i → g (p1 i)) rem1 (λ i → g y) (t x1)
      fill1 i j = primComp (λ _ → A) _ (λ k → λ { (i = i1) → t x1 (j ∧ k)
                                                        ; (i = i0) → g y
                                                        ; (j = i0) → g (p1 i) })
                                   (g (p1 i))
  
      fill2 : Square {A = A} (λ k → g y) p rem0 rem1
      fill2 = λ i → λ j → primComp (λ _ → A) _ (λ k → λ { (i = i1) → rem1 (j ∧ k)
                                                        ; (i = i0) → rem0 (j ∧ k)
                                                        ; (j = i0) → g y })
                                   (g y)
  
      sq  : Square {A = A} (λ _ → g y) (λ i → g (f (p i)))
                           (λ j → g (p0 j)) (λ j → g (p1 j))
      sq  = λ i → λ j → primComp (λ _ → A) _ (λ k → λ { (i = i1) → fill1 j (~ k)
                                                      ; (i = i0) → fill0 j (~ k)
                                                      ; (j = i1) → t (p i) (~ k)
                                                      ; (j = i0) → g y })
                                 (fill2 i j)
  
      sq1 : Square {A = B} (λ _ → y) (λ i → f (p i)) p0 p1
      sq1 = λ i → λ j → primComp (λ _ → B) _ (λ k → λ { (i = i1) → s (p1 j) k
                                                      ; (i = i0) → s (p0 j) k
                                                      ; (j = i1) → s (f (p i)) k
                                                      ; (j = i0) → s y k })
                                 (f (sq i j))
    
      lemIso : _≡_ {A = fiber f y} (x0 , p0) (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = sq1 i
  
  gradLemma : isEquiv A B f
  gradLemma y .fst .fst = g y
  gradLemma y .fst .snd i = s y (~ i)
  gradLemma y .snd z = lemIso y (g y) (fst z) (λ i → s y (~ i)) (snd z)


module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (w : A ≃ B) where
  invEq : (y : B) → A
  invEq y = fst (fst (snd w y))

  secEq : (x : A) → invEq (fst w x) ≡ x
  secEq x = λ i → fst (snd (snd w (fst w x)) (x , (λ j → fst w x)) i)

  retEq : (y : B) → fst w (invEq y) ≡ y
  retEq y = λ i → snd (fst (snd w y)) (~ i)

isoToPath : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (g : B → A)
  (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) → A ≡ B
isoToPath f g s t = equivToPath (_ , gradLemma f g s t)

invEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
invEquiv {A} {B} f = invEq f , gradLemma (invEq f) (fst f) (secEq f) (retEq f)

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
  invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
  invEquivInvol f = λ i → fst f , (propIsEquiv (fst f)
                                               (snd (invEquiv (invEquiv f)))
                                               (snd f) i)
