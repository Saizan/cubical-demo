{-# OPTIONS --cubical --caching #-}
module Cubical.CoEqualizer where


open import Cubical.PushOut
open import Cubical.FromStdLib
open import Cubical.PathPrelude
open import Cubical.Lemmas
open import Cubical.Comp
open import Cubical.SigmaDirect

data _⊎_ {l} (A B : Set l) : Set l where
  left : A → A ⊎ B
  right : B → A ⊎ B

either : ∀ {l} {A B C : Set l} → (A → C) → (B → C) → A ⊎ B → C
either f g (left x) = f x
either f g (right x) = g x

module TheCoEq {l} (A B : Set l) (f g : A → B) where

  CoEq = P {A = A} {B = B} {C = A ⊎ A} (either (\ x → x) (\ x → x)) (either f g)

  coeq : B → CoEq
  coeq = inr

  push' = push {A = A} {B = B} {C = A ⊎ A} {either (\ x → x) (\ x → x)} {either f g}

  htrans : ∀ {x y z : CoEq} → (p : x ≡ y) (q : y ≡ z) → x ≡ z
  htrans {x} p q i = primPushOutHComp _ (\ { k (i = i0) → x; k (i = i1) → q k}) (inc (p i))

  coeq-path : ∀ x → coeq (f x) ≡ coeq (g x)
  coeq-path x = htrans (sym (push' (left x))) (push' (right x))

  hfill : {φ : I} → (u : (i : I) → Partial φ CoEq) → (a0 : CoEq [ φ ↦ u i0 ])
         → PathP (\ _ → CoEq) (ouc a0)
                   (primPushOutHComp _ (λ { i (φ = i1) → u i itIsOne }) a0)

  hfill {φ} u a0 i = primPushOutHComp _
                       (\ { j (φ = i1) → u (i ∧ j) itIsOne; j (i = i0) → ouc a0 })
                        (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} a0))

  htrans-id : ∀ {x y} → (p : x ≡ y) → htrans p (\ i → y) ≡ p
  htrans-id {x} {y} p i j = hfill
                                             (λ { i (j = i0) → x
                                                ; i (j = i1) → y })
                                             (inc (p j))
                                             (~ i)

  htransf : ∀ {x y z : CoEq} → (p : x ≡ y) (q : y ≡ z) → Square _ _ _ _
  htransf {x} p q i j = hfill (\ { k (i = i0) → x; k (i = i1) → q k}) (inc (p i)) j


  module Rec {l'} {C : Set l'} (h : B → C) ([h] : ∀ x → h (f x) ≡ h (g x)) where

    coeq-elim : CoEq → C
    coeq-elim = primPushOutElim (\ _ → C) (\ a → h (f a)) h \ { (left x) → refl ; (right x) → [h] x }

    coeq-elim-path' : ∀ x → Path {A = _ ≡ _} (\ i → trans (sym refl) ([h] x) i) ([h] x)
    coeq-elim-path' x = trans-id-l ([h] x)

    coeq-elim-path : ∀ x → Path {A = _ ≡ _} (\ i → coeq-elim (coeq-path x i)) ([h] x)
    coeq-elim-path x = coeq-elim-path' x

  module Elim {l'} {C : CoEq → Set l'} (h : (x : B) → C (coeq x)) ([h] : ∀ x → PathP (\ i → C (coeq-path x i)) (h (f x)) (h (g x))) where
     module _ {ℓ'}(let A = CoEq) (P : A → Set ℓ') (sq : I → I → CoEq)
                  {a0 a1 b0 b1} (u : PathP (\ i → P (sq i i0)) a0 a1) (v : PathP (\ i → P(sq i i1)) b0 b1)
                                (r0 : PathP (\ j → P (sq i0 j)) a0 b0)
                        where
       fillSq : (i j : I) → P (sq i j)
       fillSq i j = comp (λ k → P (sq (i ∧ k) j))
                         (\ k → \ { (j = i0) → u (i ∧ k); (j = i1) → v (i ∧ k) })
                         (inc (r0 j))
       compSq : PathP _ _ _
       compSq i = fillSq i1 i

     module _ {ℓ'}(let A = CoEq) (P : A → Set ℓ') {a0 a1 : CoEq} (a01 : a0 ≡ a1) {a2} (a12 : a1 ≡ a2) {x y z}
               (xy : PathP (\ i → P (a01 (~ i))) x y) (yz : PathP (\ i → P (htrans a01 a12 i)) y z)
               where
       trans-Over-01 : PathP (\ i → P (a12 i)) x z
       trans-Over-01 = compSq P (\ i j → htransf a01 a12 i j) (\ i → xy (~ i)) yz refl

     module _ {ℓ'}(let A = CoEq) (P : A → Set ℓ') {a0 a1 : CoEq} (a01 : a0 ≡ a1) {a2} (a12 : a1 ≡ a2) {x y z}
              (xy : PathP (\ i → P (a01 i)) x y) (yz : PathP (\ i → P (a12 i)) y z) where
       trans-Over-12 : PathP (\ i → P (htrans a01 a12 i)) x z
       trans-Over-12 = compSq P (\ i j → htransf a01 a12 j i) refl yz xy

     cancel : ∀{ℓ'}(let A = CoEq) (P : A → Set ℓ') {a0 a1 : CoEq} (a01 : a0 ≡ a1) {a2} (a12 : a1 ≡ a2) {x y z}
                  → (fl : PathP (\ i → P (a01 i)) x y)
                  → (h : PathP (\ i → P (htrans a01 a12 i)) x z)
                  →        (trans-Over-12 P a01 a12 fl (trans-Over-01 P a01 a12 (\ i → fl (~ i)) h)) ≡ h
     cancel P a01 a12 fl h = Gen.lemma (\ i j → htransf a01 a12 i j) _ refl _ h _ fl
        where
         module Gen where
           lemma : ∀   (sq : I → I → CoEq) {w}
                     (x : _)
                     (s : PathP (λ j → P (sq i0 j)) w x)
                     (z : _)
                     (h : PathP (\ i → P (sq i i1)) x z)
                     (y : _)
                     (fl : PathP (\ i → P (sq i i0)) w y)
                     → (compSq P (\ i j → sq j i) s (compSq P (\ i j → sq i j) fl h s) fl) ≡ h
           lemma sq = squareJ
                      (λ sq₁ →
                         ∀ {w} x₁ (s : PathP (λ j → P (sq₁ i0 j)) w x₁) z₁
                           (h₁ : PathP (λ i → P (sq₁ i i1)) x₁ z₁) y₁
                           (fl₁ : PathP (λ i → P (sq₁ i i0)) w y₁) →
                         compSq P (λ i j → sq₁ j i) s (compSq P (λ i j → sq₁ i j) fl₁ h₁ s)
                         fl₁
                         ≡ h₁)
                      sq (pathJ _ (pathJ _ (pathJ _ (trans (trans-id-l _) (trans-id-l _)))))


     coeq-elim : ∀ (x : CoEq) → C x
     coeq-elim = primPushOutElim C (\ a → transp (\ i → C (push' (left a) (~ i))) (h (f a))) h
                                 \ { (left x) → \ i → Cubical.Comp.fill (λ i → C (push' (left x) (~ i))) i0 (\ _ → empty) (inc (h (f x))) (~ i)
                                   ; (right x) →
                                     trans-Over-01 C ((sym (push' (left x)))) (push' (right x))
                                              (\ i → Cubical.Comp.fill (λ i → C (push' (left x) (~ i))) i0 (\ _ → empty) (inc (h (f x))) (~ i))
                                              ([h] x)  }

     coeq-elim-beta : ∀ b → coeq-elim (coeq b) ≡ h b
     coeq-elim-beta b = refl

     private
       coeq-elim-path' : ∀ b → PathP (\ i → PathP (\ i → C (coeq-path b i)) (h (f b)) (h (g b)))
             -- (\ i → coeq-elim (htrans (sym (push' (left b))) (push' (right b))  i))
             (\ i → trans-Over-12 C (sym (push' (left b))) (push' (right b))
                                   (\ i → Cubical.Comp.fill (λ i → C (push (left b) (~ i))) i0 (\ _ → empty) (inc (h (f b))) i)
                    (trans-Over-01 C ((sym (push' (left b)))) (push' (right b))
                                   (\ i → Cubical.Comp.fill (λ i → C (push' (left b) (~ i))) i0 (\ _ → empty) (inc (h (f b))) (~ i))
                                   ([h] b))
                    i)
                                   ([h] b)
       coeq-elim-path' b = cancel C (sym (push' (left b))) (push' (right b)) _ ([h] b)

     coeq-elim-path : ∀ b → PathP (\ i → PathP (\ i → C (coeq-path b i)) (h (f b)) (h (g b))) (\ i → coeq-elim (coeq-path b i)) ([h] b)
     coeq-elim-path b = coeq-elim-path' b
