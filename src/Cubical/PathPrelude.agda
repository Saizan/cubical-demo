{-# OPTIONS --cubical #-}
module Cubical.PathPrelude where

open import Cubical.Primitives public
open import Cubical.Primitives public using () renaming (Sub to _[_↦_])
open import Cubical.FromStdLib
open import Cubical.NType public using (isContr ; isProp ; isSet)
open import Cubical.Sub

module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  trans' : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans' {y = y} p q i = primComp (λ _ → A) _
                                 (λ { j (i = i0) → p (~ j)
                                    ; j (i = i1) → q j })
                                 y

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q i = primComp (λ _ → A) _ (λ { j (i = i0) → x
                                                ; j (i = i1) → q j }) (p i)

  -- Dependent version of the above.
  cong-d : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
    → (f : (a : A) → B a) → (p : PathP (λ _ → A) x y)
    → PathP (λ i → B (p i)) (f x) (f y)
  cong-d f p = λ i → f (p i)

  cong : ∀ {ℓ'} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong = cong-d

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

fill = Fill
transp : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → A i0 → A i1
transp A x = primComp A i0 (λ _ → empty) x

transp⁻¹ : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → A i1 → A i0
transp⁻¹ A = transp (λ i → A (~ i))

toPathP : ∀{ℓ}{A : I → Set ℓ}{x : A i0}{y : A i1} → transp A x ≡ y → PathP A x y
toPathP {ℓ} {A} {x} {y} p i = primComp (λ _ → A i) φ u (xPathP i)
  where φ = ~ i ∨ i
        u : I → PartialP φ (λ z → A i)
        u _ (i = i0) = x
        u j (i = i1) = p j
        xPathP : PathP A x (transp A x )
        xPathP j = fill A _ (λ _ → empty) (inc x) j

fromPathP : ∀{ℓ}{A : I → Set ℓ}{x : A i0}{y : A i1} → PathP A x y → transp A x ≡ y
fromPathP {A = A} {x} {y} p  j = primComp (\ i → A i) j (\ { i (j = i1) → p i }) x

transp-refl : ∀{ℓb} → {B : Set ℓb} → (x : B) → transp (\ i → B) x ≡ x
transp-refl {B = B} x i = primComp (λ _ → B) i ((λ { j (i = i1) → x })) x

primTransp-refl : ∀{ℓb} → {B : Set ℓb} → (x : B) → primTransp (\ i → B) i0 x ≡ x
primTransp-refl {B = B} x i = primTransp (\ i → B) i x

transp-pi : ∀{ℓb} → {B : Set ℓb} → {ℓa : I → Level} → (A : (i : I) → Set (ℓa i)) → (f : (B → A i0)) → (λ x → transp A (f x)) ≡ transp (λ i → (B → A i)) f
transp-pi {B = B} A f i x = (primComp A i0 (λ i → empty)) (f (primTransp (\ _ → B) (~ i) x))


transp-iso : ∀{ℓ}(A : I → Set ℓ)(x : A i0) → transp (\ i → A (~ i)) (transp A x) ≡ x
transp-iso A x = \ i → primComp (\ j → A (~ j ∧ ~ i)) i (\ { j (i = i1) → x })
                             (primComp (\ j → A (j ∧ ~ i)) i (\ { j (i = i1) → x }) x)

transp-iso' : ∀{ℓ}(A : I → Set ℓ)(x : A i1) → PathP A (transp (\ i → A (~ i)) x) x
transp-iso' A x = toPathP {A = A} (transp-iso (λ i → A (~ i)) x)

module _ {ℓ} {A : Set ℓ} where
  singl : (a : A) → Set ℓ
  singl a = Σ[ x ∈ A ] (a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → _≡_ {A = singl a} (a , refl) (b , p)
  contrSingl p = λ i → ((p i) , λ j → p (i ∧ j))

module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x ((λ i → x))) where
  pathJ : (y : A) → (p : x ≡ y) → P y p
  pathJ _ p = transp (λ i → uncurry P (contrSingl p i)) d

  pathJprop : pathJ _ refl ≡ d
  pathJprop i = primComp (λ _ → P x refl) i (λ {j (i = i1) → d}) d

module _ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} where
  subst : {a b : A} (p : Path a b) → P a → P b
  subst {a} {b} p p0 = pathJ {ℓ} {ℓ'} (λ (y : A) → λ _ → P y) p0 b p

  substInv : {a x : A} (p : Path a x) → P x → P a
  substInv p  =  subst (λ i → p (~ i))

  subst-prop : ∀ {a} (b : A) (p : Path a b) → (x : P a) → PathP (\ i → P (p (~ i))) (subst p x) x
  subst-prop = pathJ _ \ x → pathJprop (\ y eq → P y) x

module _ {ℓ} {A : Set ℓ} {a : A}  where
  -- | `refl` is a neutral element for substitution.
  subst-neutral : subst (refl {x = a}) a ≡ a
  subst-neutral = pathJprop {x = a} (λ _ _ → A) a

injective : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → Set (ℓ-max ℓa ℓb)
injective {_} {_} {A} f = {a0 a1 : A} → f a0 ≡ f a1 → a0 ≡ a1

module _ {ℓ} {A0 A1 : Set ℓ} (A : A0 ≡ A1) {φ : I} (a0 : A i0)
         (p : Partial φ (Σ A1 λ y → PathP (λ i → A i) a0 y)) where
  -- primComp using only Path
  compP : A i1
  compP = primComp (λ i → A i) φ (λ i o → p o .snd i) a0

  -- fill using only Path
  fillP : ∀ j → A j
  fillP j = primComp (λ i → A (i ∧ j)) (φ ∨ ~ j)
    (λ { i (φ = i1) → p itIsOne .snd (i ∧ j); i (j = i0) → a0 }) a0

transpP : ∀ {ℓ ℓ'} {A : Set ℓ}{B : A → Set ℓ'} {x y : A} → x ≡ y → B x → B y
transpP {B = B} p = pathJ (λ y _ → B _ → B y) (λ x → x) _ p

module _ {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} {x y : A} (p : x ≡ y) where
  transpP≡subst : transpP {B = B} p ≡ subst {P = B} p
  transpP≡subst = sym (transp-pi (λ j → uncurry (λ (y : A) → λ _ → B y) (contrSingl p j)) (λ x → x))

  transpP≡subst' : {b : B x} → transpP {B = B} p b ≡ subst {P = B} p b
  transpP≡subst' {b} i = transpP≡subst i b

coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe {A = A} = transpP {B = λ X → X}

module _ {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} {q : A ≡ B} where
  coe-lem : (p : PathP (λ i → q i) a b) → coe q a ≡ b
  coe-lem p = trans {y = subst q a} (λ i → transpP≡subst q i a) (fromPathP p)

  coe-lem-inv : coe q a ≡ b → PathP (λ i → q i) a b
  coe-lem-inv p = toPathP (trans lem p)
    where
    lem : transp (λ i → q i) a ≡ coe q a
    lem = pathJ (λ B' q' → (transp (λ i → q' i) a) ≡ (coe q' a)) (cong (λ x → transp (λ _ → A) x) (\ i → primTransp (\ _ → A) (~ i) a)) B q

module _ {ℓa ℓb} {A : Set ℓa} {B : A → Set ℓb} where
  funUnImp : ({x : A} → B x) → (x : A) → B x
  funUnImp f x = f {x}

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p = λ i x → p x i

  funExtImp : {f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) →
                                       {x : A} → f {x} ≡ g {x}
  funExtImp p {x} = λ i → p x i

module _ {ℓ} {A : Set ℓ} where
  contr : isContr A → (φ : I) → (u : Partial φ A) → A
  contr (c , p) φ u = primComp (λ _ → A) φ (λ i o → p (u o) i) c

  lemContr : (contr1 : ∀ φ → Partial φ A → A)
             → (contr2 : ∀ u → u ≡ (contr1 i1 λ { _ → u})) → isContr A
  lemContr contr1 contr2 = x , (λ y → let module M = Aux y in
      trans (contr2 x) (trans (λ i → M.v i) (sym (contr2 y))))
    where x = contr1 i0 empty
          module Aux (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial φ A
            u = λ { (i = i0) → x ; (i = i1) → y }
            v = contr1 φ u

  contrIsProp : isContr A → isProp A
  contrIsProp h a b i = primComp (λ _ → A) _ (λ j →
    \ { (i = i0) → snd h a j; (i = i1) → snd h b j }) (fst h)

open import Agda.Builtin.Cubical.Glue public renaming
  ( prim^glue to glue
  ; prim^unglue to unglue
  ; isEquiv to isEquivR)

open Helpers public using (fiber)

module isEquiv = isEquivR

isEquiv : ∀ {ℓ ℓ'} → (A : Set ℓ) → (B : Set ℓ') → (A → B) → Set _
isEquiv A B f = isEquivR f

Glue : ∀ {ℓ ℓ'} (A : Set ℓ) → (φ : I) → (T : Partial φ (Set ℓ'))
  (f : (PartialP φ (λ o → T o ≃ A))) → Set ℓ'
Glue A φ T f = primGlue A T f

-- | The isomorphism going in the opposite direction induced by an equivalence.
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  inverse : A ≃ B → B → A
  inverse (_ , eqv) b = fst (fst (eqv .equiv-proof b))

-- The identity equivalence
idIsEquiv : ∀ {ℓ} → (A : Set ℓ) → isEquivR (λ (a : A) → a)
equiv-proof (idIsEquiv A) y = (y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j)

idEquiv : ∀ {ℓ} → {A : Set ℓ} → A ≃ A
idEquiv {A = A} = (λ a → a) , idIsEquiv A

equivToPath : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
equivToPath {_} {A} {B} f i = Glue B (~ i ∨ i)
  (λ {(i = i0) → A ; (i = i1) → B})
  (λ {(i = i0) → f ; (i = i1) → idEquiv})

module DerivedComp where
  forward : (la : I → Level) (A : ∀ i → Set (la i)) (r : I) → A r → A i1
  forward la A r x = primTransp (\ i → A (i ∨ r)) r x

  comp : (la : I → Level) (A : ∀ i → Set (la i)) (φ : I) → (u : ∀ i → Partial φ (A i)) → (u0 : A i0 [ φ ↦ u i0 ]) → A i1
  comp la A φ u u0 = primHComp (\ i → \ { (φ = i1) → forward la A i (u i itIsOne) }) (forward la A i0 (ouc u0))


Square : ∀ {ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A}
          (u : a0 ≡ a1) (v : b0 ≡ b1) (r0 : a0 ≡ b0) (r1 : a1 ≡ b1) → Set ℓ
Square {A = A} u v r0 r1 = PathP (λ i → (u i ≡ v i)) r0 r1

hfill : ∀ {ℓ} (A : Set ℓ) {φ : I}
          (u : ∀ i → Partial φ A)
          (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill A {φ = φ} u u0 i = primHComp (λ j → \ { (φ = i1) → u (i ∧ j) itIsOne ; (i = i0) → ouc u0 }) (ouc u0)


transp-equiv : ∀ {ℓ} {A B : Set ℓ} → (e : A ≃ B) → ∀ x → transp (\ i → equivToPath e i) x ≡ (e .fst x)
transp-equiv {A = A} {B = B} e x = trans (\ i → hfill B (\ _ → empty) (inc (transp (\ _ → B) (transp (\ _ → B) (e .fst x)))) (~ i))
                                  (trans (transp-refl {B = B} _)
                                         (transp-refl {B = B} _))
