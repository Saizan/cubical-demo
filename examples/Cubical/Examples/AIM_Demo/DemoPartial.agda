{-# OPTIONS --cubical #-}
module Cubical.Examples.AIM_Demo.DemoPartial where

open import Cubical.FromStdLib
open import Cubical.PathPrelude hiding (trans)



-- "Partial φ A"  is a special version of "(φ = i1) → A"

const : ∀ {A : Set} → A → ∀ (φ : I) → Partial φ A
const b φ (φ = i1) = b

myempty : ∀ {A : Set} → Partial i0 A
myempty = empty


endpoints : ∀ {A B : Set} → A → B
                                                --- Partial Set (i ∨ ~ i)
            → ∀ i → PartialP {ℓ-zero} (i ∨ ~ i) (\ { (i = i1) → A; (i = i0) → B })
endpoints {A} {B} x y i (i = i1) = x
endpoints {A} {B} x y i (i = i0) = y


endpoints-must-match' : ∀ {A : Set} → A → A → ∀ i (j : I) → Partial i A
endpoints-must-match' {A} x y i j _ = y


endpoints-must-match : ∀ {A : Set} → A → A → ∀ i j → Partial (i ∨ j) A
endpoints-must-match {A} x y i j (i = i1) = x
endpoints-must-match {A} x y i j (j = i1) = x


foo : ∀ i → Partial (i ∨ ~ i) Bool
foo i (i = i1) = true
foo i (i = i0) = false

bar : ∀ i → Partial (i ∨ ~ i) Bool
bar i (i = i0) = false
bar i (i = i1) = true


test-foo-bar : ∀ i → (P : Partial (i ∨ ~ i) Bool → Set) → P (foo i) → P (bar i)
test-foo-bar i P pfoo = pfoo











trans : ∀ {a} {A : Set a} → {x y z : A} → Path x y → Path y z → Path x z
trans {A = A} {x} {y} p q = \ i → primComp (λ j → A) _ -- (i ∨ ~ i)
                                           (\ j → \ { (i = i1) → q j
                                                    ; (i = i0) → x
                                                    }
                                           )
                                             (p i)
