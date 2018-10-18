module Cubical.Examples.Int where

open import Cubical.FromStdLib
open import Cubical.PathPrelude
open import Cubical.IsoToEquiv

data Int : Set where
  pos    : (n : ℕ) → Int
  negsuc : (n : ℕ) → Int

sucℤ : Int → Int
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : Int → Int
predℤ (pos zero)      = negsuc zero
predℤ (pos (suc n))   = pos n
predℤ (negsuc n)      = negsuc (suc n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)       = refl
sucPred (pos (suc n))    = refl
sucPred (negsuc zero)    = refl
sucPred (negsuc (suc n)) = refl

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos zero)       = refl
predSuc (pos (suc n))    = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

suc-equiv : Σ _ (isEquiv Int Int)
suc-equiv .fst = sucℤ
suc-equiv .snd = isoToEquiv sucℤ predℤ sucPred predSuc

sucPathℤ : Int ≡ Int
sucPathℤ = equivToPath suc-equiv
