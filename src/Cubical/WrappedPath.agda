{-# OPTIONS --cubical --postfix-projections #-}
module Cubical.WrappedPath where
open import Cubical.FromStdLib
open import Cubical.Primitives hiding (PathP; _≡_; Path)
import Cubical.PathPrelude as P

record PathP {ℓ} (A : I → Set ℓ) (x : A i0) (y : A i1) : Set ℓ where
  constructor con
  field
    at : P.PathP A x y

open PathP public

infix 4 _≡_

_≡_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Set ℓ
_≡_ {A = A} x y = PathP (\ _ → A) x y

Path = _≡_
module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x = x} .at = P.refl

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p .at = λ i → p .at (~ i)

  trans' : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans' {y = y} p q .at i = primComp (λ _ → A) _
                                 (λ { j (i = i0) → p .at (~ j)
                                    ; j (i = i1) → q .at j })
                                 y

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q .at i = primComp (λ _ → A) _ (λ { j (i = i0) → x
                                                ; j (i = i1) → q .at j }) (p .at i)

  cong : ∀ {ℓ'} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f p .at = λ i → f (p .at i)

  infix  3 _≡-qed _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 ≡-proof_ begin_

  ≡-proof_ begin_ : {x y : A} → x ≡ y → x ≡ y
  ≡-proof x≡y = x≡y
  begin_ = ≡-proof_

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≡-qed _∎ : (x : A) → x ≡ x
  _ ≡-qed  = refl
  _∎ = _≡-qed


fill : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  ((i : I) → Partial (A i) φ) → A i0 → (i : I) → A i
fill A φ u a0 i = unsafeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
  (λ j → unsafePOr φ (~ i) (u (i ∧ j)) λ { (i = i0) → a0 }) a0

transp : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → A i0 → A i1
transp A x = primComp A i0 (λ _ → empty) x

transp⁻¹ : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → A i1 → A i0
transp⁻¹ A = transp (λ i → A (~ i))

toPathP : ∀{ℓ}{A : I → Set ℓ}{x : A i0}{y : A i1} → transp A x ≡ y → PathP A x y
toPathP {ℓ} {A} {x} {y} p .at i = primComp (λ _ → A i) φ u (xPathP .at i)
  where φ = ~ i ∨ i
        u : I → PartialP φ (λ z → A i)
        u _ (i = i0) = x
        u j (i = i1) = p .at j
        xPathP : PathP A x (transp A x)
        xPathP .at j = fill A _ (λ _ → empty) x j

fromPathP : ∀{ℓ}{A : I → Set ℓ}{x : A i0}{y : A i1} → PathP A x y → transp A x ≡ y
fromPathP {A = A} {x} {y} p  .at j = primComp (\ i → A i) j (\ { i (j = i1) → p .at i }) x

transp-refl : ∀{ℓb} → {B : Set ℓb} → (x : B) → primComp (λ j → B) i0 (λ j → empty) x ≡ x
transp-refl {B = B} x .at i = primComp (λ _ → B) i ((λ { j (i = i1) → x })) x

transp-pi : ∀{ℓb} → {B : Set ℓb} → {ℓa : I → Level} → (A : (i : I) → Set (ℓa i)) → (f : (B → A i0)) → (λ x → transp A (f x)) ≡ transp (λ i → (B → A i)) f
transp-pi {B = B} A f .at i x = (primComp A i0 (λ i → empty)) (f (transp-refl  x .at (~ i)))

transp-iso : ∀{ℓ}(A : I → Set ℓ)(x : A i0) → transp (\ i → A (~ i)) (transp A x) ≡ x
transp-iso A x .at = \ i → primComp (\ j → A (~ j ∧ ~ i)) i (\ { j (i = i1) → x })
                             (primComp (\ j → A (j ∧ ~ i)) i (\ { j (i = i1) → x }) x)

module _ {ℓ} {A : Set ℓ} where
  singl : (a : A) → Set ℓ
  singl a = Σ[ x ∈ A ] (a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → _≡_ {A = singl a} (a , refl) (b , p)
  contrSingl p .at = λ i → ((p .at i) , λ { .at j → p .at (i ∧ j)})

module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where
  pathJ : (y : A) → (p : x ≡ y) → P y p
  pathJ _ p = transp (λ i → uncurry P (contrSingl p .at i)) d

  pathJprop : pathJ _ refl ≡ d
  pathJprop .at i = primComp (λ _ → P x refl) i (λ {j (i = i1) → d}) d

module _ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} where
  subst : {a b : A} (p : a ≡ b) → P a → P b
  subst {a} {b} p p0 = pathJ {ℓ} {ℓ'} (λ (y : A) → λ _ → P y) p0 b p

  substInv : {a x : A} (p : Path a x) → P x → P a
  substInv p  =  subst (λ { .at i → p .at (~ i)})

injective : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → Set (ℓ-max ℓa ℓb)
injective {_} {_} {A} f = {a0 a1 : A} → f a0 ≡ f a1 → a0 ≡ a1

module _ {ℓ} {A0 A1 : Set ℓ} (A : A0 ≡ A1) {φ : I} (a0 : A .at i0)
         (p : Partial (Σ A1 λ y → PathP (λ i → A .at i) a0 y) φ) where
  -- primComp using only Path
  compP : A .at i1
  compP = primComp (λ i → A .at i) φ (λ i o → p o .snd .at i) a0

  -- fill using only Path
  fillP : ∀ j → A .at j
  fillP j = primComp (λ i → A .at (i ∧ j)) (φ ∨ ~ j)
    (λ { i (φ = i1) → p itIsOne .snd .at (i ∧ j); i (j = i0) → a0 }) a0

transpP : ∀ {ℓ ℓ'} {A : Set ℓ}{B : A → Set ℓ'} {x y : A} → x ≡ y → B x → B y
transpP {B = B} p = pathJ (λ y _ → B _ → B y) (λ x → x) _ p

transpP≡subst : ∀ {ℓ ℓ'} {A : Set ℓ}{B : A → Set ℓ'} {x y : A} → (p : x ≡ y) → transpP {B = B} p ≡ subst {P = B} p
transpP≡subst {A = A} {B} {x} {y} p = sym (transp-pi (λ j → uncurry (λ (y : A) → λ _ → B y) (contrSingl p .at j)) (λ x → x))

coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe {A = A} = transpP {B = λ X → X}

module _ {ℓa ℓb} {A : Set ℓa} {B : A → Set ℓb} where
  funUnImp : ({x : A} → B x) → (x : A) → B x
  funUnImp f x = f {x}

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p .at i x = p x .at i

  funExtImp : {f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) →
                                       {x : A} → f {x} ≡ g {x}
  funExtImp p {x} .at i = p x .at i

module _ {ℓ} (A : Set ℓ) where
  isContr : Set ℓ
  isContr = Σ[ x ∈ A ] (∀ y → x ≡ y)

  isProp  : Set ℓ
  isProp  = (x y : A) → x ≡ y

  isSet   : Set ℓ
  isSet   = (x y : A) → (p q : x ≡ y) → p ≡ q

module _ {ℓ} {A : Set ℓ} where
  contr : isContr A → (φ : I) → (u : Partial A φ) → A
  contr (c , p) φ u = primComp (λ _ → A) φ (λ i o → p (u o) .at i) c

  lemContr : (contr1 : ∀ φ → Partial A φ → A)
             → (contr2 : ∀ u → u ≡ (contr1 i1 λ { _ → u})) → isContr A
  lemContr contr1 contr2 = x , (λ y → let module M = Aux y in
      trans (contr2 x) (trans (λ { .at i → M.v i }) (sym (contr2 y))))
    where x = contr1 i0 empty
          module Aux (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial A φ
            u = λ { (i = i0) → x ; (i = i1) → y }
            v = contr1 φ u

  contrIsProp : isContr A → isProp A
  contrIsProp h a b .at i = primComp (λ _ → A) _ (λ j →
    \ { (i = i0) → snd h a .at j; (i = i1) → snd h b .at j }) (fst h)

module _ {ℓ ℓ' : I → Level} {T : ∀ i → Set (ℓ i)} {A : ∀ i → Set (ℓ' i)}
         (f : ∀ i → T i → A i) (φ : I) (t : ∀ i → Partial (T i) φ)
         (t0 : T i0 {- [ φ ↦ t i0 ] -}) where
  private
    c1 c2 : A i1
    c1 = unsafeComp A φ (λ i → (λ { (φ = i1) → f i (t i itIsOne)})) (f i0 t0)
    c2 = f i1 (unsafeComp T φ t t0)

    a0 = f i0 t0

    a : ∀ i → Partial (A i) φ
    a i = (λ { (φ = i1) → f i ((t i) itIsOne)})

    u : ∀ i → A i
    u = fill A φ a a0

    v : ∀ i → T i
    v = fill T φ t t0

  pres : c1 ≡ c2
  pres .at j = unsafeComp A (φ ∨ (j ∨ ~ j)) (λ i → primPOr φ (j ∨ ~ j)
    (a i) \ { (j = i1) → f i (v i); (j = i0) → u i}) a0

fiber : ∀ {ℓ ℓ'} {E : Set ℓ} {B : Set ℓ'} (f : E → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {E = E} f y = Σ[ x ∈ E ] y ≡ f x

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  isEquiv : (A → B) → Set (ℓ-max ℓ ℓ')
  isEquiv f = (y : B) → isContr (fiber f y)

  infix 4 _≃_
  _≃_ = Σ _ isEquiv

  module _ (f : _≃_) (φ : I) (t : Partial A φ) (a : B {- [ φ ↦ f t ] -})
           (p : PartialP φ (λ o → a ≡ fst f (t o))) where
    equiv : fiber (fst f) a -- [ φ ↦ (t , λ j → a) ]
    equiv = contr ((snd f) a) φ (λ o → t o , (λ { .at i → p o .at i}))

    equivFunc : A
    equivFunc = fst equiv

    equivProof : a ≡ fst f equivFunc
    equivProof = snd equiv


module _ {ℓ} {A B : Set ℓ} (f : A ≃ B) where

  theEquiv : A P.≃ B
  fst theEquiv = f .fst
  snd theEquiv y .fst .fst = f .snd y .fst .fst
  snd theEquiv y .fst .snd i = f .snd y .fst .snd .at i
  theEquiv .snd y .snd y' i .fst = f .snd y .snd ((y' .fst) , (con \ i → y' .snd i)) .at i .fst
  theEquiv .snd y .snd y' i .snd j = f .snd y .snd ((y' .fst) , (con \ i → y' .snd i)) .at i .snd .at j

  equivToPath : A ≡ B
  equivToPath .at i = P.equivToPath theEquiv i
