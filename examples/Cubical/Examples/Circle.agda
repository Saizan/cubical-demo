{-# OPTIONS --cubical #-}

module Cubical.Examples.Circle where

open import Cubical.FromStdLib
open import Cubical.PathPrelude hiding (trans)
open import Cubical.Rewrite

open import Cubical.Examples.Int

data S¹   : Set where
  base : S¹
  loop : base ≡ base

module S¹Elim {ℓ} {P : S¹ → Set ℓ} (base* : P base)
    (loop* : PathP (λ i → P (loop i)) base* base*) where
    S¹-elim : ∀ x → P x
    S¹-elim base = base*
    S¹-elim (loop i) = loop* i

open S¹Elim public

helix : S¹ → Set
helix = S¹-elim Int sucPathℤ

π¹S¹ : Set
π¹S¹ = base ≡ base

coerce : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coerce p a = primTransp (λ i → p i) i0 a

winding : base ≡ base → Int
winding p = coerce (λ i → helix (p i)) (pos zero)

compS¹ : {x y z : S¹} → x ≡ y → y ≡ z → x ≡ z
compS¹ {x} p q i = primHComp (λ { _ (i = i0) → x; j (i = i1) → q j }) (p i)

posLoop : ℕ → base ≡ base
posLoop zero = refl
posLoop (suc n) = compS¹ (posLoop n) loop

negLoop : ℕ → base ≡ base
negLoop zero = sym loop
negLoop (suc n) = compS¹ (negLoop n) (sym loop)

intLoop : Int → base ≡ base
intLoop (pos n) = posLoop n
intLoop (negsuc n) = negLoop n

decodeSquarePos : (n : ℕ) → Square refl loop (intLoop (predℤ (pos n))) (intLoop (pos n))
decodeSquarePos zero i j = loop (i ∨ ~ j)
decodeSquarePos (suc n) i j = hfill S¹ (\ k → \ { (j = i0) → base ; (j = i1) → loop k } ) (inc (posLoop n j)) i

decodeSquareNeg : (n : ℕ) → Square refl loop (intLoop (negsuc (suc n))) (intLoop (negsuc n))
decodeSquareNeg n i j = primHComp (λ k → λ { (i = i1) → negLoop n j ; (j = i0) → base ; (j = i1) → loop (i ∨ ~ k) }) (negLoop n j)

decodeSquare : (n : Int) → Square refl loop (intLoop (predℤ n)) (intLoop n)
decodeSquare (pos n) = decodeSquarePos n
decodeSquare (negsuc n) = decodeSquareNeg n

decode : (x : S¹) → helix x → base ≡ x
decode base = intLoop
decode (loop i) y j =
  let n : Int
      n = unglue {φ = i ∨ ~ i} y
  in primHComp (λ k → \ { (j = i0) → base
                        ; (j = i1) → loop i
                        ; (i = i0) → intLoop (predSuc y k) j
                        ; (i = i1) → intLoop y j})
               (decodeSquare n i j )

encode : ∀ x → base ≡ x → helix x
encode x p = coerce (λ i → helix (p i)) (pos zero)

decodeEncode : (x : S¹) (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p = coerce (\ i → decode (p i) (encode (p i) (\ j → p (i ∧ j))) ≡ (\ j → p (i ∧ j))) refl


-- a test case.
five = suc (suc (suc (suc (suc zero))))

test-winding-pos : winding (intLoop (pos five)) ≡ pos five
test-winding-pos = refl

test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
test-winding-neg = refl


