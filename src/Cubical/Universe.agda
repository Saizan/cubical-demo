-- See §3.5 in [HoTT]
module Cubical.Universe where

open import Cubical.FromStdLib

open import Cubical.NType

module _ {ℓ : Level} where
  _-type : TLevel → Set (ℓ-suc ℓ)
  n -type = Σ (Set ℓ) (HasLevel n)

  hSet : Set (ℓ-suc ℓ)
  hSet = ⟨0⟩ -type

  Prop : Set (ℓ-suc ℓ)
  Prop = ⟨-1⟩ -type
