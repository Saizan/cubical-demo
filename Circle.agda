{-# OPTIONS --cubical --rewriting #-}
module Circle where
open import PathPrelude
open import Univalence
open import Int
open import Rewrite

postulate
  S¹ : Set
  base : S¹
  loop : base ≡ base

module S¹Elim {ℓ} {P : S¹ → Set ℓ} (base* : P base)
    (loop* : PathP (λ i → P (loop i)) base* base*) where
  postulate
    S¹-elim : ∀ x → P x
    -- postulating the reductions from the cubicaltt paper
    comp1 :              Rewrite (S¹-elim base)     base*
    comp2 : ∀ i →        Rewrite (S¹-elim (loop i)) (loop* i)
    comp3 : ∀ {φ u u0} → Rewrite (S¹-elim (unsafeComp (λ i → S¹) φ u u0))
                           (unsafeComp (λ i → P (fill (λ i → S¹) φ u u0 i))
                                       φ
                                       (λ i → λ { _ → S¹-elim (u i itIsOne) })
                                       (S¹-elim u0))

open S¹Elim public

{-# REWRITE comp1 #-}
{-# REWRITE comp2 #-}
{-# REWRITE comp3 #-}


helix : S¹ → Set
helix = S¹-elim Int (λ i → sucPathℤ i)

coerce : ∀ {ℓ} {A B : Set ℓ} → Path A B → A → B
coerce p a = primComp (λ i → p i) i0 (λ _ → empty) a

winding : base ≡ base → Int
winding p = coerce (λ i → helix (p i)) (pos zero)

natLoop : Nat → base ≡ base
natLoop zero = refl
natLoop (suc n) = trans loop (natLoop n)

intLoop : Int → base ≡ base
intLoop (pos n) = natLoop n
intLoop (negsuc n) = sym (natLoop (suc n))


-- a test case.
five = suc (suc (suc (suc (suc zero))))

-- TODO
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Internal.hs:985

-- test-winding-pos : winding (intLoop (pos five)) ≡ pos five
-- test-winding-pos = refl

-- test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
-- test-winding-neg = refl
