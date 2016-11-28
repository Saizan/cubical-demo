{-# OPTIONS --cubical  #-}
module Id where

open import Level
open import PathPrelude
open import Sub
open import Primitives

-- conid is safe too, but here we have everything expressed in the type.
safeConId : ∀ {a} {A : Set a} {x : A} φ {y : Sub {A = A} φ r[ x ]} → (w : Sub {A = Path x (ouc y)} φ r[ (\ _ → x) ]) → Id x (ouc y)
safeConId φ {y} w = conid φ (ouc w)

primitive
 primIdElim :
   ∀ {a p} {A : Set a}{x : A}
          (P : ∀ y → Id x y →  Set p) →
          (∀ φ (y : Sub {A = A} φ (\ o → x)) --- y : A [ φ ↦ x ]
              → (w : Sub φ r[ (\ i → x) ]) → P (ouc y) (conid φ (ouc w)))
           → ∀ (y : A) (w : Id x y) → P y w


elimId = primIdElim

idPath : ∀ {a} {A : Set a}{x y : A} → Id x y → Path x y
idPath {x = x} {y = y} = elimId (λ y _ → Path x y) (λ φ y₁ w → ouc w) _

star : ∀ {a} {A : Set a}{x : A} → ∀ i y → (w : Id x y) → Id x (idPath w ∙ i)
star {a} {A} {x} i = elimId _ (λ φ y w → let
                                 y' : Sub (φ ∨ (~ i)) (\ _ → x)
                                 y' = inc (ouc w i)
                                 r : Sub {a} {A = Path x (ouc w i)} (φ ∨ (~ i)) ([ (φ) ↦ r[ (\ i → x) ] , ~ i ↦ r[ (\ i → x) ] ])
                                 r = (inc {A = Path x (ouc w ∙ i)} {φ = φ ∨ (~ i)} ((\ j → ouc w (i ∧ j))))
                                 -- eq : ouc y' ≡ (ouc w i)
                                 -- eq = {!!}
                                 -- z : Id x (ouc w i)
                                 -- z = safeConId {A = A} {x} (φ ∨ ~ i) {y'} r
                             in  conid (φ ∨ ~ i) (ouc r) ) where


myJ : ∀ {a p} {A : Set a}{x : A}(P : ∀ y → Id x y → Set p) → P x (safeConId i1 {inc x} (inc (\ i → x))) → ∀ y w → P y w
myJ {A = A} {x} P d = elimId _ (λ φ y w →
        primComp (λ i → P (ouc w ∙ i) (safeConId ((φ ∨ ~ i)) {inc (ouc w i)} ((inc {A = Path x (ouc w ∙ i)} {φ = φ ∨ (~ i)} ((\ j → ouc w (i ∧ j)))))))
               φ (\ i → r[ d ]  ) d )


ap-with-J : ∀ {a} {A B : Set a} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
ap-with-J f x = myJ (λ y _ → Id (f x) (f y)) (conid i1 _)

apI : ∀ {a} {A B : Set a} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
apI {a} {A} {B} f x = elimId (λ y _ → Id (f x) (f y))
  (λ φ y w →
     conid φ
       (λ j →
       primComp (λ i → B) (φ ∨ ((~ j) ∨ j))
       (λ i' →
         primPOr φ ((~ j) ∨ j) (λ o → f x)
         (primPOr (~ j) j (λ _ → f x) (λ _ → f (ouc w i'))))
           (f x)))

test-apI : ∀ {a} {A B : Set a} (f : A → B) (x y : A) (p : Id x y) → ap-with-J f x y p ≡ apI f x y p
test-apI f x y p = refl

congI : ∀ {a} {A B : Set a} (f : A → B) (x y : A) → Id x y → Id (f x) (f y)
congI f x = elimId (λ y _ → Id (f x) (f y)) (λ φ y w → conid φ (\ i → f (ouc w i)))

transI : ∀ {a} {A : Set a} {x} (y : A) → Id x y → (z : A) → Id y z → Id x z
transI {A = A} {x} = elimId _ \ φp y p → elimId _ λ φq z q →
      primComp (\ i → Id x (ouc q i)) (φp ∨ φq) (\ i → [ φp ↦ r[ conid (φq ∨ ~ i) (\ k → ouc q (k ∧ i)) ]
                                                       , φq ↦ r[ conid φp (ouc p) ] ])
                                        (conid φp (ouc p))
-- transI reflId (safeConId φ w) = (safeConId φ w)
-- transI (safeConId φ w) reflId = (safeConId φ w)

test∨ : ∀ {a b}(P : I → Set) → P (a ∨ b) → P (a ∨ b)
test∨ P x = x
