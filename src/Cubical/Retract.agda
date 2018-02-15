module Cubical.Retract where

open import Cubical
open import Cubical.FromStdLib

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  section : (f : A → B) → (g : B → A) → Set ℓb
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Set ℓa
  retract f g = ∀ a → g (f a) ≡ a

  lemRetract : (f : A → B) → (g : B → A) → retract f g → injective (g ∘ f)
  lemRetract f g rfg {x} {y} eq = trans (sym (rfg x)) (trans eq (rfg y))

  retractProp : (f : A → B) → (g : B → A) → retract f g → isProp B → isProp A
  retractProp f g rfg pB x y = lemRetract f g rfg (cong g (pB (f x) (f y)))

  retractInv : (f : A → B) → (g : B → A) → retract f g → injective f
  retractInv f g rfg eq = lemRetract f g rfg (cong g eq)

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  HasSection : (A → B) → Set (ℓ-max ℓa ℓb)
  HasSection r = Σ (B → A) (λ s → retract s r)

module _ {ℓa ℓb : Level} (A : Set ℓa) (B : Set ℓb) where
  IsRetract : Set (ℓ-max ℓa ℓb)
  IsRetract = Σ (A → B) HasSection

  retractPresContr : IsRetract → isContr A → isContr B
  retractPresContr (r , s , ε) (a , contr) = r a , λ b →
    let
      h : r (s b) ≡ b
      h = ε b
      h' : a ≡ s b
      h' = contr (s b)
      h'' : r (s b) ≡ r a
      h'' = cong r (sym h')
      res : r a ≡ b
      res = trans (sym h'') h
    in res

  retractPresProp : IsRetract → isProp A → isProp B
  retractPresProp (r , s , ε) propA = retractProp s r ε propA

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  fromEquiv : A ≃ B → IsRetract A B
  fromEquiv (f , eqv-f) = f , a , r
    where
      module _ (b : B) where
        fbr : fiber f b
        fbr = fst (eqv-f b)
        a : A
        a = fst fbr
        eq : b ≡ f a
        eq = snd fbr
        -- aka `retract f g`
        r : f a ≡ b
        r = sym eq
