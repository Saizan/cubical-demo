{-# OPTIONS --cubical #-}
module Cubical.AIM_Demo.DemoPartial where

open import Level renaming (zero to lzero)
open import Cubical.PathPrelude hiding (trans)

open import Data.Bool hiding (_∨_; _∧_)


-- "Partial A φ"  is a special version of "(φ = i1) → A"

const : ∀ {A : Set} → A → ∀ (φ : I) → Partial A φ
const b φ (φ = i1) = b

myempty : ∀ {A : Set} → Partial A i0
myempty = empty

                                                                    --- Partial Set (i ∨ ~ i)
endpoints : ∀ {A B : Set} → A → B → ∀ i → PartialP {lzero} (i ∨ ~ i) (\ { (i = i1) → A; (i = i0) → B })
endpoints {A} {B} x y i (i = i1) = x
endpoints {A} {B} x y i (i = i0) = y


endpoints-must-match' : ∀ {A : Set} → A → A → ∀ i (j : I) → Partial A i
endpoints-must-match' {A} x y i j _ = y


endpoints-must-match : ∀ {A : Set} → A → A → ∀ i j → Partial A (i ∨ j)
endpoints-must-match {A} x y i j (i = i1) = x
endpoints-must-match {A} x y i j (j = i1) = x


foo : ∀ i → Partial Bool (i ∨ ~ i)
foo i (i = i1) = true
foo i (i = i0) = false

bar : ∀ i → Partial Bool (i ∨ ~ i)
bar i (i = i0) = false
bar i (i = i1) = true


test-foo-bar : ∀ i → (P : Partial Bool (i ∨ ~ i) → Set) → P (foo i) → P (bar i)
test-foo-bar i P pfoo = pfoo











trans : ∀ {a} {A : Set a} → {x y z : A} → Path x y → Path y z → Path x z
trans {A = A} {x} {y} p q = \ i → primComp (λ j → A) _ -- (i ∨ ~ i)
                                           (\ j → \ { (i = i1) → q j
                                                    ; (i = i0) → x
                                                    }
                                           )
                                             (p i)
