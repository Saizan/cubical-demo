module retract where

open import PathPrelude

section : ∀{A B : Set} → (f : A → B) → (g : B → A) → Set
section f g = ∀ b → f (g b) ≡ b

retract : ∀{A B : Set} → (f : A → B) → (g : B → A) → Set
retract f g = ∀ a → g (f a) ≡ a

lemRetract : ∀ {A B : Set} → (f : A → B) → (g : B → A) → retract f g → injective (g ∘ f)
lemRetract f g rfg {x} {y} eq = trans (sym (rfg x)) (trans eq (rfg y))

retractProp : ∀ {A B : Set} → (f : A → B) → (g : B → A) → retract f g → isProp B → isProp A
retractProp f g rfg pB x y = lemRetract f g rfg (cong g (pB (f x) (f y)))

retractInv : ∀ {A B : Set} → (f : A → B) → (g : B → A) → retract f g → injective f
retractInv f g rfg eq = lemRetract f g rfg (cong g eq)
