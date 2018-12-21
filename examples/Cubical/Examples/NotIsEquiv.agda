module Cubical.Examples.NotIsEquiv where

open import Cubical.PathPrelude
open import Cubical.FromStdLib

not : Bool → Bool
not true = false
not false = true

notnot : ∀ y → not (not y) ≡ y
notnot true = refl
notnot false = refl

nothelp : ∀ y (y₁ : Σ Bool (λ x → Path (not x) y)) →
          Path (not y , notnot y) y₁
nothelp y (true , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (true , eq')) refl _ (eq)
nothelp y (false , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (false , eq')) refl _ (eq)


notIsEquiv : isEquiv Bool Bool not
notIsEquiv = (\ { .equiv-proof y → (not y , notnot y) , nothelp y })
