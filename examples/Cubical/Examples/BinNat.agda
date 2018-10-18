{-# OPTIONS --cubical #-}
module Cubical.Examples.BinNat where

open import Cubical.Examples.CTT.Data.Nat

open import Cubical.FromStdLib
open import Cubical.PathPrelude
open import Cubical.IsoToEquiv
open import Cubical.Univalence

data Pos : Set where
  pos1 : Pos
  x0 : Pos -> Pos
  x1 : Pos -> Pos


sucPos : Pos → Pos
sucPos pos1 = x0 pos1
sucPos (x0 ps) = x1 ps
sucPos (x1 ps) = x0 (sucPos ps)


doubleN : ℕ → ℕ
doubleN zero = zero
doubleN (suc x) = suc (suc (doubleN x))

posToN : Pos → ℕ
posToN pos1 = suc zero
posToN (x0 ps) = doubleN (posToN ps)
posToN (x1 ps) = suc ( doubleN ( posToN ps))

posInd : {P : Pos → Set} → (h1 : P pos1) → (hs : (p : Pos) → P p → P (sucPos p)) → (p : Pos) → P p
posInd {P} h1 hs ps = f ps where
  H : (p : Pos) → (hx0p : P (x0 p)) → P (x0 (sucPos p))
  H p hx0p = hs (x1 p) (hs (x0 p) hx0p)

  f : (ps : Pos) → P ps
  f pos1 = h1
  f (x0 ps) = posInd (hs pos1 h1) H ps
  f (x1 ps) = hs (x0 ps) (posInd (hs pos1 h1) H ps)


sucPosSuc : (p : Pos) → posToN (sucPos p) ≡ suc (posToN p)
sucPosSuc pos1 = refl
sucPosSuc (x0 p) = refl
sucPosSuc (x1 p) = cong doubleN (sucPosSuc p)


zeronPosToN : (p : Pos) → ¬ (zero ≡ posToN p)
zeronPosToN p = posInd (λ prf → znots zero prf) hs p where
  hs : (p : Pos) → ¬ (zero ≡ posToN p) → zero ≡ posToN (sucPos p) → ⊥
  hs p neq ieq = ⊥-elim (znots (posToN p) (trans ieq (sucPosSuc p)))

ntoPos' : ℕ → Pos
ntoPos' zero = pos1
ntoPos' (suc n) = sucPos (ntoPos' n)

ntoPos : ℕ → Pos
ntoPos zero = pos1
ntoPos (suc n) = ntoPos' n


posToNK : ∀ n → posToN (ntoPos (suc n)) ≡ suc n
posToNK zero = λ x → 1
posToNK (suc n) = trans (sucPosSuc (ntoPos' n)) ih where
  ih = cong suc (posToNK n)

ntoPosSuc : ∀ n → ¬ (zero ≡ n) → ntoPos (suc n) ≡ sucPos (ntoPos n)
ntoPosSuc zero neq = ⊥-elim (neq refl)
ntoPosSuc (suc n) neq = refl

ntoPosK : (p : Pos) → ntoPos (posToN p) ≡ p
ntoPosK p = posInd refl hs p where
  hs : (p : Pos) → ntoPos (posToN p) ≡ p → ntoPos (posToN (sucPos p)) ≡ sucPos p
  hs p hp = trans (trans h1 h2) h3 where
    h1 = cong ntoPos (sucPosSuc p)
    h2 = ntoPosSuc (posToN p) (zeronPosToN p)
    h3 = cong sucPos hp

posToNinj : injective posToN
posToNinj {a0} {a1} eq = λ i → primComp (λ _ → Pos) _ (λ { j (i = i0) → ntoPosK a0 j
                                                         ; j (i = i1) → ntoPosK a1 j }) (ntoPos (eq i))
data BinN : Set where
  binN0 : BinN
  binNpos : Pos → BinN

ntoBinN : ℕ → BinN
ntoBinN zero = binN0
ntoBinN (suc n) = binNpos (ntoPos (suc n))

binNtoN : BinN → ℕ
binNtoN binN0 = zero
binNtoN (binNpos x) = posToN x

ntoBinNK : (n : ℕ) → binNtoN (ntoBinN n) ≡ n
ntoBinNK zero = refl
ntoBinNK (suc n) = posToNK n


lem1 : ∀ p → ntoBinN (posToN p) ≡ binNpos p
lem1 p = posInd refl (λ p _ → rem p) p where
  rem : (p : Pos) → ntoBinN (posToN (sucPos p)) ≡ binNpos (sucPos p)
  rem p = trans rem1 rem2 where
    rem1 = cong ntoBinN (sucPosSuc p)
    rem2 : binNpos (ntoPos (suc (posToN p))) ≡ binNpos (sucPos p)
    rem2 = λ i → binNpos (trans (ntoPosSuc (posToN p) (zeronPosToN p)) (cong sucPos (ntoPosK p)) i)


binNtoNK : ∀ b → ntoBinN (binNtoN b) ≡ b
binNtoNK binN0 = refl
binNtoNK (binNpos x) = lem1 x

eqBinNN : BinN ≡ ℕ
eqBinNN = isoToPath binNtoN ntoBinN ntoBinNK binNtoNK

-- doublesN n m = 2^n * m
doublesN : ℕ → ℕ → ℕ
doublesN zero m = m
doublesN (suc n) m = doublesN n (doubleN m)

-- 1024 = 2^8 * 2^2 = 2^10
n1024 : ℕ
n1024 = doublesN (4 + 4) 4

doubleBinN : BinN → BinN
doubleBinN binN0 = binN0
doubleBinN (binNpos x) = binNpos (x0 x)

doublesBinN : ℕ → BinN → BinN
doublesBinN zero b = b
doublesBinN (suc n) b = doublesBinN n (doubleBinN b)


-- Doubling structure
data Double : Set (ℓ-suc ℓ-zero) where
  dC : (A : Set)           -- carrier
      → (double : A -> A) -- doubling function computing 2 * x
      → (elt : A)         -- element to double
      → Double

carrier : Double -> Set
carrier (dC c _ _) = c

double : (D : Double) -> (carrier D -> carrier D)
double (dC _ op _) = op

elt : (D : Double) -> carrier D
elt (dC _ _ e) = e

DoubleN : Double
DoubleN = dC ℕ doubleN n1024

bin1024 : BinN
bin1024 = binNpos (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 pos1))))))))))

DoubleBinN : Double
DoubleBinN = dC BinN doubleBinN bin1024

-- iterate
iter : {A : Set} → ℕ → (A → A) → A → A
iter zero f z = z
iter (suc n) f z = f (iter n f z)

-- Compute: 2^n * x
doubles : ∀ D → (n : ℕ) → carrier D → carrier D
doubles D n x = iter n (double D) x

-- 2^20 * e = 2^5 * (2^15 * e)

propDouble : Double → Set
propDouble D = doubles D 20 (elt D) ≡ doubles D 5 (doubles D 15 (elt D))

-- The property we want to prove that takes long to typecheck:
-- 2^10 * 1024 = 2^5 * (2^5 * 1024)
--
-- propN : propDouble DoubleN
-- propN = refl


-- With binary numbers it is instant
propBin : propDouble DoubleBinN
propBin = refl

-- Define intermediate structure:
doubleBinN' : BinN → BinN
doubleBinN' b = ntoBinN (doubleN (binNtoN b))

DoubleBinN' : Double
DoubleBinN' = dC BinN doubleBinN' (ntoBinN n1024)

eqDouble1 : DoubleN ≡ DoubleBinN'
eqDouble1 = elimIsoInv (λ f g → DoubleN ≡ (dC _ (λ x → f (doubleN (g x))) (f n1024))) refl ntoBinN binNtoN binNtoNK ntoBinNK

eqDouble2 : DoubleBinN' ≡ DoubleBinN
eqDouble2 = cong F rem where
  F : (BinN → BinN) → Double
  F d = dC _ d (ntoBinN n1024)
  rem : doubleBinN' ≡ doubleBinN
  rem = funExt rem1 where
    rem1 : ∀ n → (doubleBinN' n) ≡ (doubleBinN n)
    rem1 binN0 i = binN0
    rem1 (binNpos x) = lem1 (x0 x)

eqDouble : DoubleN ≡ DoubleBinN
eqDouble = trans eqDouble1 eqDouble2

propDoubleImpl : propDouble DoubleBinN → propDouble DoubleN
propDoubleImpl x = subst {P = propDouble} (sym eqDouble) x

goal : propDouble DoubleN
goal = propDoubleImpl propBin
