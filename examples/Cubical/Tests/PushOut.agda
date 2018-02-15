{-# OPTIONS --cubical #-}
module Cubical.Tests.PushOut where

open import Cubical.PathPrelude
open import Cubical.Sub
open import Cubical.FromStdLib
open import Cubical.PushOut

primFwd : ∀ {l : I → Level} (A : (i : I) → Set (l i)) → (r : I) → A r → A i1
primFwd A r u = primComp (\ i → A (r ∨ i)) r (\ { j (r = i1) → u }) u

primFwdFill : ∀ {l : I → Level} (A : (i : I) → Set (l i)) → (r : I) → (u : A r) → (j : I) → A (j ∨ r)
primFwdFill A r u j = primComp (λ i → A (r ∨ (j ∧ i))) (r ∨ ~ j) (λ i → primPOr r (~ j) {A = λ _ → A (r ∨ j ∧ i)}(λ { (r = i1) → u }) (λ { (j = i0) → u })) u

module Elim {l m} {A B C : Set l} {f : C → A} {g : C → B} (M : P f g -> Set m)
                    (il : ∀ a → M (inl a)) (ir : ∀ b → M (inr b))
                    (p : ∀ c → PathP (\ i → M (push c i)) (il (f c)) (ir (g c))) where
   elim = primPushOutElim M il ir p

   test1 : ∀ {x} → elim (inl x) ≡ il x
   test1 = refl

   test2 : ∀ {x} → elim (inr x) ≡ ir x
   test2 = refl

   test3 : ∀ {c r} → elim (push c r) ≡ p c r
   test3 = refl

   open import Cubical.Comp

   module Test4 {φ} {u : I → Partial (P f g) φ} {u0 : Sub (P f g) φ (u i0)} where
     tm : M (primPushOutHComp {f = f} {g = g} φ u u0)
     tm = primComp (λ i → M (primPushOutHComp {f = f} {g = g} (φ ∨ ~ i)
                                  (\ { j (φ = i1) → u (j ∧ i) itIsOne
                                     ; j (i = i0) → ouc {A = P f g} u0 })
                                (inc {ℓ = l} {A = P f g} (ouc {A = P f g} u0))))
                                φ
             (\ { i (φ = i1) → elim (u i itIsOne)  }) (elim (ouc {A = P f g} u0))


     test4 : tm ≡ elim (primPushOutHComp {f = f} {g = g} φ u u0)
     test4 = refl


open import Cubical.FromStdLib
module PrimComp {l : I → Level} {A B C : (i : I) → Set (l i)} {f : ∀ i → C i → A i} {g : ∀ i → C i → B i}
                    (let P = \ (i : I) → P (f i) (g i))
                    (φ : I) (u : ∀ i → Partial (P i) φ) (u0 : Sub (P i0) φ (u i0)) where

   testComp : primComp P φ u (ouc u0) ≡
            primPushOutHComp {f = f i1} {g = g i1} φ
              (\ { j o → primPushOutForward {l = l} {f = f} {g = g} j (u j o) } )
              (inc (primPushOutForward {f = f} {g = g} i0 (ouc u0)))
   testComp = refl

module Forward {l : I → Level} {A B C : (i : I) → Set (l i)} {f : ∀ i → C i → A i} {g : ∀ i → C i → B i}
                    (r : I) where

     fwd' = primPushOutForward {l} {A} {B} {C} {f} {g}
     fwd = primPushOutForward {l} {A} {B} {C} {f} {g} r

     test1 : ∀ {x} → fwd (inl x) ≡ inl (primFwd A r x)
     test1 = refl

     test2 : ∀ {x} → fwd (inr x) ≡ inr (primFwd B r x)
     test2 = refl

     test3 : ∀ {c s} → fwd (push c s)
             ≡ primPushOutHComp (r ∨ (~ s ∨ s))
                   (\ { j (s = i0) →
                          fwd' (r ∨ ~ j) (inl (f (r ∨ ~ j) (primFwdFill C r c (~ j))))
                      ; j (s = i1) →
                          fwd' (r ∨ ~ j) (inr (g (r ∨ ~ j) (primFwdFill C r c (~ j))))
                      ; j (r = i1) →  push {f = f i1} c s
                      })
                   (inc {A = P (f i1) (g i1)} (push {f = f i1} (primFwd C r c) s))
     test3 = refl

     test3' : ∀ {c} → Path (fwd (inl (f r c))) (fwd (inr (g r c)))
     test3' {c} = \ s → test3 {c} {s} i1

     module Test4 {φ} {u : I → Partial (P (f r) (g r)) φ} {u0 : Sub (P (f r) (g r)) φ (u i0)} where
       test4 : fwd (primPushOutHComp φ u u0) ≡ primPushOutHComp φ (\ j o → fwd (u j o)) (inc (fwd (ouc u0)))
       test4 = refl
