module Cubical.NotIsEquiv where
open import Cubical.PathPrelude
open import Data.Bool
open import Data.Product


notnot : ∀ y → y ≡ not (not y)
notnot true = refl
notnot false = refl

nothelp : ∀ y (y₁ : Σ Bool (λ x → Path y (not x))) →
          Path (not y , notnot y) y₁
nothelp y (true , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (true , sym eq')) refl _ (sym eq)
nothelp y (false , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (false , sym eq')) refl _ (sym eq)


notIsEquiv : isEquiv Bool Bool not
notIsEquiv = (\ { y → (not y , notnot y) , nothelp y })
