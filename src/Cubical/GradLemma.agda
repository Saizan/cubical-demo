{-# OPTIONS --cubical --postfix-projections #-}
module Cubical.GradLemma where

open import Cubical
open import Cubical.FromStdLib

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

lemProp : ∀ {ℓ} {A : Set ℓ} → (A → isProp A) → isProp A
lemProp h = λ a → h a a

invEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A ≃ B) → B ≃ A
invEquiv {A} {B} f = invEq f , gradLemma (invEq f) (fst f) (secEq f) (retEq f)


module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where
  -- Π preserves propositionality in the following sense:
  propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
  propPi h f0 f1  = λ i → λ x → (h x (f0 x) (f1 x)) i

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

  invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
  invEquivInvol f = λ i → fst f , (propIsEquiv (fst f)
                                               (snd (invEquiv (invEquiv f)))
                                               (snd f) i)
