-- See §3.5 in [HoTT]
module Cubical.Universe where

open import Cubical.FromStdLib

open import Cubical.NType

module _ {ℓ : Level} where
  hSet : TLevel → Set (ℓ-suc ℓ)
  hSet n = Σ (Set ℓ) (HasLevel n)

  0-Set : Set (ℓ-suc ℓ)
  0-Set = hSet ⟨0⟩

  Prop : Set (ℓ-suc ℓ)
  Prop = hSet ⟨-2⟩
