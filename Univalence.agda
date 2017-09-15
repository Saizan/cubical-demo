{-# OPTIONS --cubical #-}
module Univalence where


open import PathPrelude hiding (_≃_; idEquiv)
open import GradLemma
open import Retract

import Function

record _≃_ {ℓa ℓb} (A : Set ℓa)(B : Set ℓb) : Set (ℓ-max ℓa ℓb) where
  no-eta-equality
  constructor con
  field
    eqv : A → B
    isEqv : isEquiv A B eqv

open _≃_


idEquiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idEquiv .eqv = idFun _
idEquiv .isEqv = (λ y → (y , refl) , contrSingl ∘ snd)

fl : ∀ {ℓ} {A : Set ℓ} → (z : A) → (primComp (λ _ → A) i0 (λ _ → empty) z) ≡ z
fl {ℓ} {A} = λ z → (λ i → primComp (λ i → A) i (λ { i _ → z }) z)

idtoeqv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {A = A} p = coe (λ i → A ≃ p i) (idEquiv {A = A})

lemEqv : ∀ {l} {A B : Set l} → (u v : A ≃ B) (p : u .eqv ≡ v .eqv) → u ≡ v
lemEqv u v p i .eqv = (p i)
lemEqv u v p i .isEqv = (lemPropF {B = isEquiv _ _} propIsEquiv p) {u .isEqv} {v .isEqv} i


[idtoeqv]refl=id : ∀ {ℓ} {A : Set ℓ} → idtoeqv {A = A} refl ≡ idEquiv
[idtoeqv]refl=id {A = A} = lemEqv _ _ ((funExt (λ z →
  trans (trans (trans (let A' = (λ _ → A)
                           r  = (transp A' (transp A' (transp A' z)))
                        in fl r) (fl _)) (fl _)) (fl z))) )


module UAEquiv
  -- To derive univalence it's sufficient to provide the following three
  -- maps, regardless of the implementation.
    (ua : ∀ {l} {A B : Set l} → A ≃ B → Path A B)
    (uaid=id : ∀ {l} {A : Set l} → Path (ua idEquiv) (λ i → A))
    (uaβ : ∀ {l} {A B : Set l} → (e : A ≃ B) → coe (ua e) ≡ e .eqv)
    {ℓ : Level} where

  lemma' : {A B : Set ℓ} (e : A ≃ B) → eqv e ≡ coe (λ i → A → ua e i) (idFun _)
  lemma' e = trans (sym (uaβ e)) (funExt λ z →
    let p : _ ≡ _
        p = sym (trans (fl _) (fl _)) in λ i → coe (ua e) (p i))

  [ua∘idtoeqv]refl≡refl : {A : Set ℓ} → (ua {A = A} {B = A} (idtoeqv {A = A} refl)) ≡ refl
  [ua∘idtoeqv]refl≡refl {A = A} = trans (λ i → ua {A = A} {B = A} ([idtoeqv]refl=id i)) uaid=id

 

  univEquiv : {A B : Set ℓ} → isEquiv (A ≡ B) (A ≃ B) idtoeqv
  univEquiv {A} {B} =
    let P = \ y z → ua {A = A} {B = y} (coe (λ i → A ≃ z i) idEquiv) ≡ z in
    gradLemma idtoeqv (ua {A = A} {B = B})
                            (λ y → lemEqv _ _ (sym (lemma' y)))
                            (pathJ P [ua∘idtoeqv]refl≡refl _)


ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua eq = equivToPath (eq .eqv , eq .isEqv)

uaid=id : ∀ {ℓ} {A : Set ℓ} → (ua idEquiv) ≡ (λ i → A)
uaid=id {A = A} = λ j → λ i → Glue A ((~ i ∨ i) ∨ j) (λ _ → A) (λ _ → idEquiv .eqv , idEquiv .isEqv)

uaβ : ∀ {ℓ} {A B : Set ℓ} → (e : A ≃ B) → coe (ua e) ≡ eqv e
uaβ e = funExt (λ x → let p = _ in trans (fl _) (trans (fl _) (trans (fl _)
                    (λ i → (eqv e) (fl p i)))))

univalence : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence .eqv = idtoeqv
univalence .isEqv = UAEquiv.univEquiv ua uaid=id uaβ

module _ where

  open module X = UAEquiv ua uaid=id uaβ

  univRetract : ∀ {ℓ} → {A B : Set ℓ} → retract {_} {_} {A ≡ B} {A ≃ B} idtoeqv ua
  univRetract {_} {A} {B} = (pathJ P [ua∘idtoeqv]refl≡refl _) where
    P = \ y z → ua {A = A} {B = y} (coe (λ i → A ≃ z i) idEquiv) ≡ z

  univSection : ∀ {ℓ} → {A B : Set ℓ} → section {_} {_} {A ≡ B} {A ≃ B} idtoeqv ua
  univSection {_} {A} {B} = (λ y → lemEqv _ _ (sym (lemma' y)))  
