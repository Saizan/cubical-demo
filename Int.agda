module Int where


open import Cube
open import GradLemma

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int


sucZ : Int → Int
sucZ (pos n) = pos (suc n)
sucZ (negsuc zero) = pos zero
sucZ (negsuc (suc n)) = negsuc n

predZ : Int → Int
predZ (pos zero) = negsuc zero
predZ (pos (suc n)) = pos n
predZ (negsuc n) = negsuc (suc n)


suc-pred : ∀ i → sucZ (predZ i) ≡ i
suc-pred (pos zero) = refl
suc-pred (pos (suc n)) = refl
suc-pred (negsuc zero) = refl
suc-pred (negsuc (suc n)) = refl

pred-suc : ∀ i → predZ (sucZ i) ≡ i
pred-suc (pos zero) = refl
pred-suc (pos (suc n)) = refl
pred-suc (negsuc zero) = refl
pred-suc (negsuc (suc n)) = refl

open import Univalence
open import GradLemma

sucPathZ : Int ≡ Int
sucPathZ = ua (sucZ , gradLemma sucZ predZ suc-pred pred-suc)
