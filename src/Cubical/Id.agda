{-# OPTIONS --cubical  #-}
module Cubical.Id where

open import Cubical.PathPrelude
open import Cubical.Sub

module _ {ℓ} {A : Set ℓ} where
  reflId : {x : A} → Id x x
  reflId {x} = conid i1 (λ _ → x)

  transId : {x y z : A} → Id x y → Id y z → Id x z
  transId {x} {y} p = J (λ y _ → Id x y) p

  pathToId : {x y : A} → x ≡ y → Id x y
  pathToId p = conid i0 (λ i → p i)

module _ {ℓ ℓ'} {A : Set ℓ} where
  congId : {B : Set ℓ'} (f : A → B) → ∀ {x y} → Id x y → Id (f x) (f y)
  congId f {x} {y} = J (λ y _ → Id (f x) (f y)) reflId

  Jdef : {x : A} (P : ∀ y → Id x y → Set ℓ') (d : P x reflId) → J P d reflId ≡ d
  Jdef P d = refl

conid' : ∀ {ℓ} {A : Set ℓ} {x : A} φ {y : A [ φ ↦ (λ { _ → x}) ]}
           → (w : Sub (x ≡ ouc y) _ λ { (φ = i1) → (λ _ → x)}) → Id x (ouc y)
conid' φ {y} w = conid φ (λ i → ouc w i)

elimId : ∀ {ℓ ℓ'} {A : Set ℓ}{x : A} (P : ∀ y → Id x y → Set ℓ') →
    (∀ φ (y : A [ φ ↦ (λ{_ → x}) ]) -- y : A [ φ ↦ x ]
    → (w : _ [ φ ↦ (λ { (φ = i1) → (λ i → x)}) ]) → P (ouc y) (conid φ (ouc w)))
    → ∀ (y : A) (w : Id x y) → P y w
elimId P h y w = primIdElim P h w

module _ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ')
         (d : P x (conid' i1 {inc x} (inc (λ i → x)))) where
  myJ : ∀ y w → P y w
  myJ = elimId P (λ φ y w → primComp (λ i →
    P (ouc w i) (conid' (φ ∨ ~ i) {inc (ouc w i)} (inc (λ j → ouc w (i ∧ j)))))
    φ (λ i → λ { (φ = i1) → d}) d)

  myJdef : myJ _ reflId ≡ d
  myJdef = refl


congI : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
congI f x = elimId (λ y _ → Id (f x) (f y))
                     (λ φ y w → conid φ (λ i → f (ouc w i)))

transI : ∀ {ℓ} {A : Set ℓ} x (y : A) → Id x y → (z : A) → Id y z → Id x z
transI {A = A} x = elimId _ λ φp y p → elimId _ λ φq z q →
      primComp (λ i → Id x (ouc q i)) (φp ∨ φq)
               (λ i → λ { (φp = i1) → conid (φq ∨ ~ i) (λ k → ouc q (k ∧ i))
                        ; (φq = i1) → conid φp         (ouc p) })
               (conid φp (ouc p))


module Test {ℓ} {A : Set ℓ} {x : A} φ {y : Sub A φ (λ{_ → x})}
            (w : (x ≡ ouc y) [ φ ↦ (λ { (φ = i1) → (λ _ → x) }) ]) where
  eq : Id x (ouc y)
  eq = (conid' φ {y} w)

  testl : transI _ _ reflId _ eq ≡ eq
  testl = refl

  testr : transI _ _ eq _ reflId ≡ eq
  testr = refl
















-- idPath : ∀ {ℓ} {A : Set ℓ}{x y : A} → Id x y → Path x y
-- idPath {x = x} {y = y} = elimId (λ y _ → Path x y) (λ φ y₁ w → ouc w) _

-- test∨ : ∀ {a b}(P : I → Set) → P (a ∨ b) → P (a ∨ b)
-- test∨ P x = x

-- ap-with-J : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
-- ap-with-J f x = myJ (λ y _ → Id (f x) (f y)) (conid i1 _)

-- apI : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
-- apI {ℓ} {A} {B} f x = elimId (λ y _ → Id (f x) (f y))
--   (λ φ y w →
--      conid φ
--        (λ j →
--        primComp (λ i → B) (φ ∨ ((~ j) ∨ j))
--        (λ i' →
--          primPOr φ ((~ j) ∨ j) (λ o → f x)
--          (primPOr (~ j) j (λ _ → f x) (λ _ → f (ouc w i'))))
--            (f x)))

-- test-apI : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (x y : A) (p : Id x y) → ap-with-J f x y p ≡ apI f x y p
-- test-apI f x y p = {!!}
