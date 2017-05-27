{-# OPTIONS --cubical  #-}
module Id where

open import Level
open import PathPrelude
open import Sub
open import Primitives


conid' : ∀ {a} {A : Set a} {x : A} φ {y : Sub {A = A} φ (\ {_ → x})}
         → (w : Sub {A = Path x (ouc y)} φ \ { _ → (\ _ → x) }) → Id x (ouc y)
conid' φ {y} w = conid φ (\ i → ouc w i)

primitive
  primIdElim : ∀ {a p} {A : Set a}{x : A}
          (P : ∀ y → Id x y → Set p) →
          (∀ φ (y : Sub {A = A} φ (\{_ → x})) --- y : A [ φ ↦ x ]
              → (w : Sub φ (\ { _ → (\ i → x)})) → P (ouc y) (conid φ (ouc w)))
           → ∀ (y : A) (w : Id x y) → P y w


elimId = primIdElim

myJ : ∀ {a p} {A : Set a}{x : A}(P : ∀ y → Id x y → Set p) → P x (conid' i1 {inc x} (inc (\ i → x))) →
      ∀ y w → P y w
myJ {A = A} {x} P d
  = elimId _ (λ φ y w →
      primComp (λ i → P (ouc w ∙ i) (conid' (φ ∨ ~ i) {inc (ouc w i)} (inc (\ j → ouc w (i ∧ j)))))
               φ (\ i → \ { _ → d}) d)


myJdef : ∀ {a p} {A : Set a}{x : A}(P : ∀ y → Id x y → Set p)
         → (d : P x (conid' i1 {inc x} (inc (\ i → x))))
         → myJ P d _ reflId ≡ d
myJdef P d = refl


congI : ∀ {a} {A B : Set a} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
congI f x = elimId (λ y _ → Id (f x) (f y)) (λ φ y w → conid φ (\ i → f (ouc w i)))

transI : ∀ {a} {A : Set a} {x} (y : A) → Id x y → (z : A) → Id y z → Id x z
transI {A = A} {x} = elimId _ \ φp y p → elimId _ λ φq z q →
      primComp (\ i → Id x (ouc q i)) (φp ∨ φq)
               (\ i → \ { (φp = i1) → conid (φq ∨ ~ i) (\ k → ouc q (k ∧ i))
                        ; (φq = i1) → conid φp         (ouc p) })
               (conid φp (ouc p))


module Test {a} {A : Set a} {x : A} φ {y : Sub {A = A} φ (\{_ → x})}
            (w : Sub {A = Path x (ouc y)} φ \ { _ → (\ _ → x) }) where

  eq : Id x (ouc y)
  eq = (conid' φ {y} w)

  testl : transI _ reflId _ eq ≡ eq
  testl = refl

  testr : transI _ eq _ reflId ≡ eq
  testr = refl















-- idPath : ∀ {a} {A : Set a}{x y : A} → Id x y → Path x y
-- idPath {x = x} {y = y} = elimId (λ y _ → Path x y) (λ φ y₁ w → ouc w) _





-- test∨ : ∀ {a b}(P : I → Set) → P (a ∨ b) → P (a ∨ b)
-- test∨ P x = x

-- ap-with-J : ∀ {a} {A B : Set a} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
-- ap-with-J f x = myJ (λ y _ → Id (f x) (f y)) (conid i1 _)

-- apI : ∀ {a} {A B : Set a} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
-- apI {a} {A} {B} f x = elimId (λ y _ → Id (f x) (f y))
--   (λ φ y w →
--      conid φ
--        (λ j →
--        primComp (λ i → B) (φ ∨ ((~ j) ∨ j))
--        (λ i' →
--          primPOr φ ((~ j) ∨ j) (λ o → f x)
--          (primPOr (~ j) j (λ _ → f x) (λ _ → f (ouc w i'))))
--            (f x)))

-- test-apI : ∀ {a} {A B : Set a} (f : A → B) (x y : A) (p : Id x y) → ap-with-J f x y p ≡ apI f x y p
-- test-apI f x y p = {!!}
