{-# OPTIONS --cubical  #-}
module Cubical.Univalence where

open import Cubical hiding (_≃_; idEquiv)
open import Cubical.FromStdLib
open import Cubical.GradLemma
open import Cubical.Retract
open import Cubical.NType.Properties using (lemPropF ; propIsEquiv ; propSet)



record _≃_ {ℓa ℓb} (A : Set ℓa)(B : Set ℓb) : Set (ℓ-max ℓa ℓb) where
  no-eta-equality
  constructor con
  field
    eqv : A → B
    isEqv : isEquiv A B eqv

  open isEquiv isEqv public

open _≃_


idEquiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idEquiv .eqv = idFun _
idEquiv .isEqv = Cubical.idEquiv .snd


idtoeqv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {A = A} p = coe (λ i → A ≃ p i) (idEquiv {A = A})

lemEqv : ∀ {l} {A B : Set l} → (u v : A ≃ B) (p : u .eqv ≡ v .eqv) → u ≡ v
lemEqv u v p i .eqv = (p i)
lemEqv u v p i .isEqv = (lemPropF {B = isEquiv _ _} propIsEquiv p) {u .isEqv} {v .isEqv} i


[idtoeqv]refl=id : ∀ {ℓ} {A : Set ℓ} → idtoeqv {A = A} refl ≡ idEquiv
[idtoeqv]refl=id {A = A} = lemEqv _ _ ((funExt (λ z →
  trans (trans (trans (let A' = (λ _ → A)
                           r  = (transp A' (transp A' (transp A' z)))
                        in transp-refl r) (transp-refl _)) (transp-refl _)) (transp-refl z))) )


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
        p = sym (trans (transp-refl _) (transp-refl _)) in λ i → coe (ua e) (p i))

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
uaβ e = funExt (λ x → let p = _ in trans (transp-refl _) (trans (transp-refl _) (trans (transp-refl _)
                    (λ i → (eqv e) (transp-refl p i)))))

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



-- The formalization is due to Fabian Ruch.
univalenceAlt : ∀ {ℓ} → {B : Set ℓ} → isContr (Σ (Set ℓ) (λ X → X ≃ B))
univalenceAlt {B = B} = (B , idEquiv) , prf where
  prf : (y : Σ _ (λ X → X ≃ B)) → (B , idEquiv) ≡ y
  prf (A , A≃B) = subst {P = λ z → (B , idEquiv) ≡ (A , z)} (univSection A≃B)
      (pathJ {x = B} (λ X B≡X → (B , idEquiv) ≡ (X , (idtoeqv (sym B≡X))))
         (sym (cong (λ z → (B , z)) [idtoeqv]refl=id)) A B≡A) where
    B≡A : B ≡ A
    B≡A = sym (ua A≃B)


------------------------------------------------------------------------------
-- Elimination principle for equivalences and isomorphisms

module _ where

  contrSinglEquiv : ∀ {ℓ} → {A : Set ℓ} → {B : Set ℓ} → (e : A ≃ B)
                    → (B , idEquiv {A = B}) ≡ (A , e)
  contrSinglEquiv {ℓ} {A} {B} e = rem where
    rem1 : isProp (Σ (Set ℓ) (λ X → X ≃ B))
    rem1 = contrIsProp univalenceAlt
    rem : (B , idEquiv) ≡ (A , e)
    rem = rem1 (B , idEquiv) (A , e)


  elimEquiv : ∀ {ℓ ℓ'} → {B : Set ℓ} (P : {A : Set ℓ} → (A → B) → Set ℓ') → (d : P (idFun B))
              → {A : Set ℓ} → (e : A ≃ B) → P (eqv e)
  elimEquiv {ℓ} {ℓ'} {B} P d {A} e = rem where
    T : (Σ (Set ℓ) (λ X → X ≃ B)) → Set ℓ'
    T x = P (eqv (snd x))
    rem1 : (B , idEquiv) ≡ (A , e)
    rem1 = contrSinglEquiv e
    rem : P (eqv e)
    rem = subst {P = T} rem1 d

  elimIso : ∀{ℓ ℓ'} → {B : Set ℓ} → (Q : {A : Set ℓ} → (A → B) → (B → A) → Set ℓ') → (h : Q (idFun B) (idFun B))
            → {A : Set ℓ} → (f : A → B) → (g : B → A) → section f g → retract f g → Q f g
  elimIso {ℓ} {ℓ'} {B} Q h {A} f g sfg rfg = rem1 f g sfg rfg where
    P : {A : Set ℓ} → (f : A -> B) → Set (ℓ-max ℓ' ℓ)
    P {A} f = (g : B -> A) -> section f g -> retract f g -> Q f g

    rem : P (idFun B)
    rem g sfg rfg = substInv {P = Q (idFun B)} (λ i → λ b → (sfg b) i) h

    rem1 : {A : Set ℓ} → (f : A -> B) → P f
    rem1 f g sfg rfg = elimEquiv P rem (con f (gradLemma f g sfg rfg)) g sfg rfg

  elimIsoInv : ∀{ℓ ℓ'} → {A : Set ℓ} → (Q : {B : Set ℓ} → (A → B) → (B → A) → Set ℓ') → (h : Q (idFun A) (idFun A))
               → {B : Set ℓ} → (f : A → B) → (g : B → A) → section f g → retract f g → Q f g
  elimIsoInv {A = A} Q h {B} f g sfg rfg = elimIso (λ f g → Q g f) h g f rfg sfg
