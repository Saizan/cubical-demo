module Cubical.Retract where

open import Cubical
open import Cubical.FromStdLib

section : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → (g : B → A) → Set ℓb
section f g = ∀ b → f (g b) ≡ b

retract : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → (g : B → A) → Set ℓa
retract f g = ∀ a → g (f a) ≡ a

lemRetract : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → (g : B → A) → retract f g → injective (g ∘ f)
lemRetract f g rfg {x} {y} eq = trans (sym (rfg x)) (trans eq (rfg y))

retractProp : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → (g : B → A) → retract f g → isProp B → isProp A
retractProp f g rfg pB x y = lemRetract f g rfg (cong g (pB (f x) (f y)))

retractInv : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → (g : B → A) → retract f g → injective f
retractInv f g rfg eq = lemRetract f g rfg (cong g eq)
