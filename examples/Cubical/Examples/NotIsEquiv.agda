module Cubical.Examples.NotIsEquiv where

open import Cubical.PathPrelude
open import Cubical.FromStdLib

not : Bool → Bool
not true = false
not false = true

notnot : ∀ y → y ≡ not (not y)
notnot true = refl
notnot false = refl

nothelp : ∀ y (y₁ : Σ Bool (λ x → Path y (not x))) →
          Path (not y , notnot y) y₁
nothelp y (true , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (true , sym eq')) refl _ (sym eq)
nothelp y (false , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (false , sym eq')) refl _ (sym eq)


notIsEquiv : isEquiv Bool Bool not
notIsEquiv = (\ { .equiv-proof y → (not y , notnot y) , nothelp y })
