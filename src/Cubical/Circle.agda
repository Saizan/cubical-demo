{-# OPTIONS --cubical --rewriting #-}
module Cubical.Circle where
open import Cubical.PathPrelude
open import Cubical.Int
open import Cubical.Rewrite

postulate
  S¹   : Set
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
                                       (λ i → λ { (φ = i1) → S¹-elim (u i itIsOne) })
                                       (S¹-elim u0))

open S¹Elim public

{-# REWRITE comp1 #-}
{-# REWRITE comp2 #-}
{-# REWRITE comp3 #-}


helix : S¹ → Set
helix = S¹-elim Int sucPathℤ

π¹S¹ : Set
π¹S¹ = base ≡ base

coerce : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coerce p a = primComp (λ i → p i) i0 (λ _ → empty) a

winding : base ≡ base → Int
winding p = coerce (λ i → helix (p i)) (pos zero)



natLoop : Nat → base ≡ base
natLoop zero = refl
natLoop (suc n) = trans (natLoop n) loop

intLoop : Int → base ≡ base
intLoop (pos n) = natLoop n
intLoop (negsuc n) = sym (natLoop (suc n))

-- a test case.
five = suc (suc (suc (suc (suc zero))))

test-winding-pos : winding (intLoop (pos five)) ≡ pos five
test-winding-pos = refl

test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
test-winding-neg = refl



-- lemFib1 : {A : Set} (F G : A -> Set) {a : A} (fa : F a -> G a) ->
--    ∀ (x : A) (p : a ≡ x) -> (fx : F x -> G x) ->
--      (Path {A = F a -> G x} (\ (u : F a) -> coerce (\ i → G (p i)) (fa u)) (\ (u : F a) -> fx (coerce (\ i → F (p i)) u)))
--      ≡ (PathP (\ i → F (p i) -> G (p i)) fa fx)
-- lemFib1 F G {a} fa = pathJ (λ y z →
--                            (fx : F y → G y) →
--                            Path (λ u → coerce (λ i → G (z i)) (fa u))
--                            (λ u → fx (coerce (λ i → F (z i)) u))
--                            ≡ PathP (λ i → F (z i) → G (z i)) fa fx)
--                        (\ ga i → Path {A = F a → G a}
--                                       (\ u → fill (\ i → G a) i0 (\ _ → empty) (fa u) (~ i) )
--                                       (\ u → ga (fill (\ i → F a) i0 (\ _ → empty) u (~ i))))

-- abstract
--   corFib1 : {A : Set} (F G : A -> Set) {a : A} (fa ga : F a -> G a)
--           (p : a ≡ a)
--           (h : (u : F a) -> Path (coerce (\ i → G (p i)) (fa u))
--                                  (ga (coerce (\ i → F (p i)) u)))
--           → PathP (\ i → F (p i) -> G (p i)) fa ga
--   corFib1 F G fa ga p h = coerce (lemFib1 F G fa _ p ga) (\ i u → h u i)


-- lemma : (u : helix base) → Path (coerce (λ i → base ≡ loop i) (intLoop u)) (intLoop (coerce (λ i → helix (loop i)) u))
-- lemma (pos zero) = refl
-- lemma (pos (suc n)) = {!!}
-- lemma (negsuc zero) = {!!}
-- lemma (negsuc (suc n)) = {!!}


-- decode : (x : S¹) → helix x → base ≡ x
-- decode = S¹-elim
--            intLoop
--            (corFib1 helix (_≡_ base) intLoop intLoop loop {!!})

-- encode : ∀ x → base ≡ x → helix x
-- encode x p = coerce (λ i → helix (p i)) (pos zero)

-- encodeDecode : (x : S¹) (p : base ≡ x) → decode x (encode x p) ≡ p
-- encodeDecode x p = coerce (\ i → decode (p i) (encode (p i) (\ j → p (i ∧ j))) ≡ (\ j → p (i ∧ j))) refl

-- decodeEncode : (z : Int) → encode base (decode base z) ≡ z
-- decodeEncode (pos zero)       = refl
-- decodeEncode (pos (suc n))    = {!!}
-- decodeEncode (negsuc zero)    = {!!}
-- decodeEncode (negsuc (suc n)) = {!!}


-- iso1 : (x : π¹S¹) → (intLoop (winding x)) ≡ x
-- iso1 x = encodeDecode _ x
