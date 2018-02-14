module Cubical.Retract where

open import Cubical
open import Cubical.Prelude

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  section : (f : A → B) → (g : B → A) → Set ℓb
  section f g = ∀ b → f (g b) ≡ b

  retract : (f : A → B) → (g : B → A) → Set ℓa
  retract f g = ∀ a → g (f a) ≡ a

  lemRetract : (f : A → B) → (g : B → A) → retract f g → injective (g ∘ f)
  lemRetract f g rfg {x} {y} eq = trans (sym (rfg x)) (trans eq (rfg y))

  retractProp : (f : A → B) → (g : B → A) → retract f g → isProp B → isProp A
  retractProp f g rfg pB x y = lemRetract f g rfg (cong g (pB (f x) (f y)))

  retractInv : (f : A → B) → (g : B → A) → retract f g → injective f
  retractInv f g rfg eq = lemRetract f g rfg (cong g eq)
