module Int where

open import Data.Product
open import PathPrelude
open import GradLemma

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

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

sucPathℤ : Int ≡ Int
sucPathℤ = equivToPath (sucℤ , gradLemma sucℤ predℤ sucPred predSuc)
