{-# OPTIONS --cubical #-}
module Univalence where

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

open import PathPrelude
open import GradLemma


transpP : ∀ {a b}{A : Set a}{B : A → Set b} {x y : A} → x ≡ y → B x → B y
transpP {B = B} p = pathJ (λ y _ → B _ → B y) (\ x → x) _ p

coe : ∀ {A B : Set} → Path A B → A → B
coe {A} = transpP {B = \ X → X}

fl : {A : Set} → (z : A) → Path (primComp (\ _ → A) i0 (\ _ → empty) z)  z
fl {A} = \ z → (\ i → fill (\ i → A) i0 (\ i → empty) z (~ i))

idtoeqv : ∀ {A B : Set} → Path A B → Equiv A B
idtoeqv {A} p = coe (\ i → Equiv A (p i)) (idEquiv {A = A})

[idtoeqv]refl=id : ∀ {A : Set} → idtoeqv {A} refl ≡ idEquiv
[idtoeqv]refl=id {A} = lemSig propIsEquiv _ _ ( (fun-ext (\ z → trans (trans (trans (
            let r = (unsafeComp (λ _ → A) i0 (λ _ → empty) (unsafeComp (λ _ → A) i0 (λ _ → empty)
                                                           (unsafeComp (λ _ → A) i0 (λ _ → empty) z)))
            in   fl r       ) (fl _)) (fl _)) (fl z))) )

module UAEquiv
     (ua : ∀ {l} {A B : Set l} → Equiv A B → Path A B)
     (uaid=id : ∀ {A : Set} → Path (ua idEquiv) (λ i → A))
     (uaβ : ∀ {A B : Set} → (e : Equiv A B) → coe (ua e) ≡ fst e)
     where

  lemma' : ∀ {A B : Set} (e : Equiv A B) → Path (fst e) (coe (λ i → A → ua e i) (λ x → x))
  lemma' e = trans (sym (uaβ e)) (fun-ext \ z → let p : Path _ _; p = sym (trans (fl _) (fl _)) in \ i → coe (ua e) (p i))


  [ua∘idtoeqv]refl≡refl : ∀ {A : Set} → Path (ua (idtoeqv {A} refl)) refl
  [ua∘idtoeqv]refl≡refl = trans (\ i → ua ([idtoeqv]refl=id i)) uaid=id

  univ-equiv : ∀ {A} {B : Set} → isEquiv (Path A B) (Equiv A B) idtoeqv
  univ-equiv {A} {B} = let P = λ y z → Path (ua (coe (λ i → Equiv A (z i)) idEquiv)) z in
                       gradLemma (λ z → coe (λ i → Equiv A (z i)) idEquiv) ua
                                   (\ y → lemSig propIsEquiv _ _ (sym (lemma' y)))
                                 (pathJ P [ua∘idtoeqv]refl≡refl _)


ua : ∀ {l} {A B : Set l} → Equiv A B → Path A B
ua = eqToPath'

uaid=id : ∀ {A : Set} → Path (ua idEquiv) (λ i → A)
uaid=id {A} =  \ j → \ i → Glue A ((~ i ∨ i) ∨ j) (λ _ → A) (\ _ → idEquiv)

uaβ : ∀ {A B : Set} → (e : Equiv A B) → coe (ua e) ≡ fst e
uaβ e = fun-ext (λ x → let p = _ in trans (fl _) (trans (fl _) (trans (fl _) (\ i → (fst e) (fl p i)))))


univalence : ∀ {A : Set} {B : Set} → isEquiv (Path A B) (Equiv A B) idtoeqv
univalence = UAEquiv.univ-equiv ua uaid=id uaβ
