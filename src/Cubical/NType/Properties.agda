{-# OPTIONS --cubical #-}
module Cubical.NType.Properties where

open import Cubical.PathPrelude
open import Cubical.FromStdLib
open import Cubical.NType
open import Cubical.Lemmas

lemProp : ∀ {ℓ} {A : Set ℓ} → (A → isProp A) → isProp A
lemProp h = λ a → h a a

module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where
  -- Π preserves propositionality in the following sense:
  propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
  propPi h f0 f1  = λ i → λ x → (h x (f0 x) (f1 x)) i

  -- `lemPropF` can be used to prove equalities in the dependent function space
  -- of propositions.
  lemPropF : (P : (x : A) → isProp (B x)) {a0 a1 : A}
    (p : a0 ≡ a1) {b0 : B a0} {b1 : B a1} → PathP (λ i → B (p i)) b0 b1
  lemPropF P p {b0} {b1} = λ i → P (p i)
     (primComp (λ j → B (p (i ∧ j)) ) (~ i) (λ _ →  λ { (i = i0) → b0 }) b0)
     (primComp (λ j → B (p (i ∨ ~ j)) ) (i) (λ _ → λ{ (i = i1) → b1 }) b1) i

  lemSig : (pB : (x : A) → isProp (B x))
    (u v : Σ A B) (p : fst u ≡ fst v) → u ≡ v
  lemSig pB u v p = λ i → (p i) , ((lemPropF pB p) {snd u} {snd v} i)

  propSig : (pA : isProp A) (pB : (x : A) → isProp (B x)) → isProp (Σ A B)
  propSig pA pB t u = lemSig pB t u (pA (fst t) (fst u))

lemSigP : ∀ {ℓ ℓ'} {A : Set ℓ} {B : (i : I) → A → Set ℓ'}
        (pB : ∀ i → (x : A) → isProp (B i x))
        (u : Σ A (B i0)) (v : Σ A (B i1)) (p : (fst u) ≡ (fst v)) → PathP (\ i → Σ A (B i)) u v
lemSigP {B = B} pB u v p i = (p i) , lemPropF (pB i) p {b0 = fill (\ j → B j (fst u)) i0 (\ _ → empty) (snd u) i}
                                                       {b1 = fill (\ j → B (~ j) (fst v)) i0 (\ _ → empty) (snd v) (~ i)} i

module _ {ℓ} {A : Set ℓ} where
  propSet : isProp A → isSet A
  propSet h = λ(a b : A) (p q : a ≡ b) j i →
    primComp (λ k → A)((~ i ∨ i) ∨ (~ j ∨ j))
      (λ k → λ { (i = i0) → h a a k; (i = i1) → h a b k
               ; (j = i0) → h a (p i) k; (j = i1) → h a (q i) k }) a

  propIsContr : isProp (isContr A)
  propIsContr = lemProp (λ t → propSig (λ a b → trans (sym (snd t a)) (snd t b))
         (λ x → propPi (propSet ((λ a b → trans (sym (snd t a)) (snd t b))) x)))

  hasLevelPath : ∀ n → HasLevel (S n) A → ∀ (x y : A) → HasLevel n (x ≡ y)
  hasLevelPath ⟨-2⟩      lvl x y = lvl x y , propSet lvl x y (lvl x y)
  hasLevelPath (S ⟨-2⟩)  lvl = lvl
  hasLevelPath (S (S n)) lvl = lvl

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
  propIsEquiv : (f : A → B) → isProp (isEquiv A B f)
  propIsEquiv f = λ u0 u1 → λ i → λ y → propIsContr (u0 y) (u1 y) i

open import Cubical.Retract

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : A → Set ℓb} where
  module _ (f g : (a : A) → B a) where
    Homotopy : Set (ℓ-max ℓa ℓb)
    Homotopy = ∀ a → f a ≡ g a

module _ {ℓ : Level} {A B : Set ℓ} where
  module _ {f g : A → A} where
    -- Just as a reminder: A retract of f and g is a homotopy between their
    -- composition and the identity function.
    fromRetract : retract f g → Homotopy (g ∘ f) λ a → a
    fromRetract r = r

private
  infixl 5 _◾_
  _◾_ = trans

private
  module _ {ℓ : Level} {A : Set ℓ} {a b c : A} {p : a ≡ b} {q : b ≡ c} where
    helper : {r : a ≡ c} → p ◾ q ≡ r → q ≡ sym p ◾ r
    helper {r} = pathJ (\ b p → (q : b ≡ c) → p ◾ q ≡ r → q ≡ sym p ◾ r) (\ q eq →
           trans (sym (trans-id-l q)) (trans eq (sym (trans-id-l r)))) b p q

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  module _ {f g : A → B} {x y : A} (H : Homotopy f g) (p : x ≡ y) where

    lem2-4-3' : cong g p ≡ sym (H x) ◾ cong f p ◾ H y
    lem2-4-3' = trans (helper (lem2-4-3 H p)) trans-assoc

-- Theorem 7.1.4 in HoTT p. 222:
transportNType : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} {n} → IsRetract A B → HasLevel n A → HasLevel n B
transportNType {A = A} {B} {⟨-2⟩}   = retractPresContr A B
transportNType {A = A} {B} {S ⟨-2⟩} = retractPresProp A B
transportNType {A = A} {B} {S (S n)} (p , (s , ε)) lvl a a' = transportNType {n = S n} r' llvl
  where
    t : s a ≡ s a' → a ≡ a'
    t q = (sym (ε a)) ◾ (cong p q) ◾ (ε a')
    r' : IsRetract (s a ≡ s a') (a ≡ a')
    r' = t , (cong s) , \ r → sym (lem2-4-3' ε r)
    llvl : HasLevel (S n) (s a ≡ s a')
    llvl = hasLevelPath (S n) lvl (s a) (s a')


module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  -- Corollary 7.1.5 in HoTT.
  equivPreservesNType : {n : TLevel} → A ≃ B → HasLevel n A → HasLevel n B
  equivPreservesNType {n} eqv = transportNType {n = n} (Cubical.Retract.fromEquiv eqv)

module _ {ℓ ℓ'} {A : Set ℓ} where
  -- Π preserves homotopy levels in the following sense:
  contrPi : {B : A → Set ℓ'} → ((x : A) → isContr (B x)) → isContr ((x : A) → B x)
  fst (contrPi h) a = fst (h a)
  snd (contrPi h) π = funExt λ x →
    let
      allEq : ∀ y → fst (h x) ≡ y
      allEq = snd (h x)
      eq : fst (h x) ≡ π x
      eq = allEq (π x)
    in eq

  -- Thm 7.1.9
  piPresNType
      : (n : TLevel)
      → {B : A → Set ℓ'}
      → ((x : A) → HasLevel n (B x))
      → HasLevel n ((x : A) → B x)
  piPresNType ⟨-2⟩      = contrPi
  piPresNType (S ⟨-2⟩)  = propPi
  piPresNType (S n@(S m)) nB f g = transportNType {n = n}
                                                  (funExt , (\ eq x i → eq i x) , (λ a → refl))
                                                  (piPresNType n (\ x → nB x (f x) (g x)))


  setPi : {B : A → Set ℓ'} → ((x : A) → isSet (B x))
        → isSet ((x : A) → B x)
  setPi = piPresNType ⟨0⟩
