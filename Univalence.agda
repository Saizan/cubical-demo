{-# OPTIONS --cubical #-}
module Univalence where

open import PathPrelude
open import GradLemma

fl : ∀ {ℓ} {A : Set ℓ} → (z : A) → (primComp (λ _ → A) i0 (λ _ → empty) z) ≡ z
fl {ℓ} {A} = λ z → (λ i → primComp (λ i → A) i (λ { i _ → z }) z)

idtoeqv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {A = A} p = coe (λ i → A ≃ p i) (idEquiv {A = A})

[idtoeqv]refl=id : ∀ {ℓ} {A : Set ℓ} → idtoeqv {A = A} refl ≡ idEquiv
[idtoeqv]refl=id {A = A} = lemSig propIsEquiv _ _ ((funExt (λ z →
  trans (trans (trans (let A' = (λ _ → A)
                           r  = (transp A' (transp A' (transp A' z)))
                        in fl r) (fl _)) (fl _)) (fl z))) )


module UAEquiv
  -- To derive univalence it's sufficient to provide the following three
  -- maps, regardless of the implementation.
    (ua : ∀ {l} {A B : Set l} → A ≃ B → Path A B)
    (uaid=id : ∀ {l} {A : Set l} → Path (ua idEquiv) (λ i → A))
    (uaβ : ∀ {l} {A B : Set l} → (e : A ≃ B) → coe (ua e) ≡ fst e)
    {ℓ : Level} where

  lemma' : {A B : Set ℓ} (e : A ≃ B) → fst e ≡ coe (λ i → A → ua e i) (idFun _)
  lemma' e = trans (sym (uaβ e)) (funExt λ z →
    let p : _ ≡ _
        p = sym (trans (fl _) (fl _)) in λ i → coe (ua e) (p i))

  [ua∘idtoeqv]refl≡refl : {A : Set ℓ} → (ua (idtoeqv {A = A} refl)) ≡ refl
  [ua∘idtoeqv]refl≡refl = trans (λ i → ua ([idtoeqv]refl=id i)) uaid=id

  univEquiv : {A B : Set ℓ} → isEquiv (A ≡ B) (A ≃ B) idtoeqv
  univEquiv {A} {B} = let P = λ y z → ua (coe (λ i → A ≃ z i) idEquiv) ≡ z
                       in gradLemma (λ z → coe (λ i → A ≃ z i) idEquiv) ua
                            (λ y → lemSig propIsEquiv _ _ (sym (lemma' y)))
                            (pathJ P [ua∘idtoeqv]refl≡refl _)

ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua = equivToPath

uaid=id : ∀ {ℓ} {A : Set ℓ} → (ua idEquiv) ≡ (λ i → A)
uaid=id {A = A} = λ j → λ i → Glue A ((~ i ∨ i) ∨ j) (λ _ → A) (λ _ → idEquiv)

uaβ : ∀ {ℓ} {A B : Set ℓ} → (e : A ≃ B) → coe (ua e) ≡ fst e
uaβ e = funExt (λ x → let p = _ in trans (fl _) (trans (fl _) (trans (fl _)
                    (λ i → (fst e) (fl p i)))))

univalence : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = idtoeqv , UAEquiv.univEquiv ua uaid=id uaβ
