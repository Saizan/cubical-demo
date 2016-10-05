{-# OPTIONS --cubical --rewriting #-}


open import Cube
open import Univalence
open import Int


postulate
  Rewrite : ∀ {l} {A : Set l} → A → A → Set

{-# BUILTIN REWRITE Rewrite #-}




postulate
  S¹ : Set
  base : S¹
  loop : base ≡ base

module S¹Elim {i} {P : S¹ → Set i} (base* : P base)
    (loop* : PathP (\ i → P (loop i)) base* base*) where
  postulate
    S¹-elim : ∀ x → P x
    -- postulating the reductions from the cubicaltt paper
    comp1 :              Rewrite (S¹-elim base)     base*
    comp2 : ∀ i →        Rewrite (S¹-elim (loop i)) (loop* i)
    comp3 : ∀ {φ u u0} → Rewrite (S¹-elim (unsafeComp (\ i → S¹) φ u u0))
                                 (unsafeComp (\ i → P (fill (\ i → S¹) φ u u0 i))
                                             φ
                                             (\ i → r[ S¹-elim (u i itIsOne) ])
                                             (S¹-elim u0))

open S¹Elim public

{-# REWRITE comp1 #-}
{-# REWRITE comp2 #-}
{-# REWRITE comp3 #-}


helix : S¹ -> Set
helix = S¹-elim Int (\ i → sucPathZ i)

coerce : ∀ {l} {A B : Set l} → Path A B → A → B
coerce p a = primComp (\ i → p i) i0 (\ _ → empty) a

winding : base ≡ base → Int
winding p = coerce (\ i → helix (p i)) (pos zero)

natLoop : Nat → base ≡ base
natLoop zero = refl
natLoop (suc n) = trans loop (natLoop n)

intLoop : Int → base ≡ base
intLoop (pos n) = natLoop n
intLoop (negsuc n) = sym (natLoop (suc n))

one two three four five : Nat
one = suc zero

two = suc one
three = suc two
four = suc three
five = suc four


test-winding-pos : winding (intLoop (pos five)) ≡ pos five
test-winding-pos = refl

test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
test-winding-neg = refl
