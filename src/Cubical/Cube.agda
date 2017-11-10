{-# OPTIONS --cubical #-}
module Cubical.Cube where

open import Cubical.PathPrelude
open import Cubical.Id

test-sym : ∀ {ℓ} {A : Set ℓ} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p
test-sym p = refl


test-bool : (p : true ≡ false) → Bool
test-bool p = primComp (λ _ → Bool) i1 (λ j → λ _ → p j) true
-- cannot reduce to true, because it's already reducing to false.

etaExpand : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → x ≡ y
etaExpand p = λ z → p z

etaEq : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → p ≡ etaExpand p
etaEq p = refl


module IntervalEquations where
  postulate
    P : I → Set
  test-0 : (P (~ i0) ≡ P i1)
  test-0 = refl
  test-1 : P (~ i1) ≡ P i0
  test-1 = refl
  test-2 : ∀ {i j} → P (~ (i ∧ j)) ≡ P (~ i ∨ ~ j)
  test-2 = refl
  test-3 : ∀ {i j} → P (~ (i ∨ j)) ≡ P (~ i ∧ ~ j)
  test-3 = refl
  test-4 : ∀ {i} → P (~ (~ i)) ≡ P i
  test-4 = refl

  test-5 : ∀ {i} → P (_∧_ i0 i) ≡ P i0
  test-5 = refl

  test-52 : ∀ {i} → P (_∧_ i i) ≡ P i
  test-52 = refl

  test-53 : ∀ {i j} → P (i ∧ j) ≡ P (j ∧ i)
  test-53 = refl

  test-n6 : ∀ {i} → P (i1 ∧ i) ≡ P i
  test-n6 = refl

  test-n7 : ∀ {i} → P (i ∧ i0) ≡ P i0
  test-n7 = refl

  test-n8 : ∀ {i} → P (i ∧ i1) ≡ P i
  test-n8 = refl

J-comp : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} {P : ∀ y → Id x y → Set ℓ'} →
         (d : P x reflId) → J P d reflId ≡ d
J-comp _ = refl

outPartial : ∀ {ℓ} {A : Set ℓ} → Partial A i1 → A
outPartial = λ f → f itIsOne

inPartial : ∀ {ℓ} {A : Set ℓ} → A → Partial A i1
inPartial a = λ _ → a

module _ {ℓ ℓ'} {A : I → Set ℓ} {B : ∀ i → A i → Set ℓ'}
         (let ℓ = _ ; C : I → Set ℓ ; C i = (x : A i) → B i x) where
  compPi : (φ : I) → (∀ i → Partial (C i) φ) → (a : C i0) → C i1
  compPi φ u a x1 = unsafeComp
      (λ i → B i (v i)) φ (λ i o → u i o (v i)) (a (v i0)) where
    v : (i : I) → A i
    v i = unsafeComp (λ j → A (i ∨ (~ j))) i (λ j → p[_] {A = A} x1 _ (~ j) ) x1
    f : ∀ i → (a : A i) → Partial (B i a) φ
    f i a = λ { (φ = i1) → u i itIsOne a  }


  compPi' : (φ : I) → (∀ i → Partial (C i) φ) → (a : C i0) → C i1
  compPi' φ u a = unsafeComp C φ u a

  test-compPi : (φ : I) → (u : ∀ i → Partial (C i) φ) → (a : C i0) →
                  compPi φ u a ≡ compPi' φ u a
  test-compPi = λ φ p p0 → refl

module _ {ℓ} {A : I → Set ℓ} (u v : ∀ i → A i) (φ : I)
         (let C = λ (i : I) → u i ≡ v i) (p : ∀ i → Partial (C i) φ) where
  compPath : C i0 → C i1
  compPath p0 = λ j → unsafeComp A (φ ∨ (~ j ∨ j))
                        (λ i → [ φ   ↦ (λ o → (p i o) j) , (~ j ∨ j) ↦
                               [ ~ j ↦ (λ _ → u i)
                               , j   ↦ (λ _ → v i) ]
                               ]) (p0 j)

  compPath' : C i0 → C i1
  compPath' = unsafeComp C φ p

  test-compPath : (p0 : C i0) → compPath p0 ≡ compPath' p0
  test-compPath p0 = refl


module TestPathP {ℓ} {A : I → I → Set ℓ} (u : ∀ i → A i i0)(v : ∀ i → A i i1)
                  (φ : I) (let C = λ (i : I) → PathP (A i) (u i) (v i))
                  (p : ∀ i → Partial (C i) φ) (p0 : C i0) where

 compPathP : C i1
 compPathP = λ j → unsafeComp (λ i → A i j) (φ ∨ (~ j ∨ j))
                     (λ i → [ φ   ↦ (λ o → (p i o) j) , (~ j ∨ j) ↦
                            [ ~ j ↦ (λ { (j = i0) → u i } )
                            , j   ↦ (λ { (j = i1) → v i } ) ]
                            ]) (p0 j)

 compPathP' : C i1
 compPathP' = unsafeComp C φ p p0

 test-compPathP : compPathP ≡ compPathP'
 test-compPathP = refl

module RecordComp where
  record R {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') (C : (x : A) → B x → Set ℓ)
     : Set (ℓ-max ℓ ℓ') where
   coinductive
   constructor _,_
   field
     fst : A
     snd : B fst
     trd : C fst snd
  open R

  {-# TERMINATING #-}
  compR : ∀ {ℓ ℓ'} {A : I → Set ℓ} {B : ∀ i → A i → Set ℓ'}
                   {C : ∀ i → (x : A i) → B i x → Set ℓ} →
    (let ℓ = _ ; Z : I → Set ℓ ; Z i = R(A i)(B i)(C i))
    (φ : I) → (∀ i → Partial (Z i) φ) → Z i0 → Z i1
  fst (compR {A = A} {B} φ w w0) =
    unsafeComp A φ (λ i →  (λ{ (φ = i1) → fst (w i itIsOne) }) ) (fst w0)
  snd (compR {A = A} {B} φ w w0) =
    unsafeComp (λ i → B i (a i)) φ (λ i → (λ { (φ = i1) → snd (w i itIsOne) })) (snd w0)
      where
        a = fill (λ z → A z) φ (λ i → (λ { (φ = i1) → fst (w i itIsOne) }) ) (fst w0)
  trd (compR {A = A} {B} {C} φ w w0) = unsafeComp
      (λ i → C i (a i) (b i)) φ ((λ i → (λ { (φ = i1) → trd (w i itIsOne)}))) (trd w0)
    where
      Z : I → Set _
      Z i = R (A i) (B i) (C i)
      z : (i : I) → _
      z i = compR {A = λ j → A (i ∧ j)} {λ j → B (i ∧ j)} {λ j → C (i ∧ j)}
        (φ ∨ ~ i) (λ j → unsafePOr {_} φ (~ i) {λ _ →
          R (A (i ∧ j)) (B (i ∧ j)) (C (i ∧ j))} (w (i ∧ j)) (λ{ (i = i0) → w0 })) w0
      --fill Z φ w w0
      a : (i : I) → _
      a i = fst (z i)
      b : (i : I) → _
      b i = snd (z i)

  module _ {ℓ ℓ'} {A : I → Set ℓ} {B : ∀ i → A i → Set ℓ'}
                  {C : ∀ i → (x : A i) → B i x → Set ℓ}
                  (let ℓ = _ ; Z : I → Set ℓ ; Z i = R(A i)(B i)(C i))
                  (φ : I) (u : ∀ i → Partial (Z i) φ) (a : Z i0) where
    test-compR-1 : fst (compR {A = A} {B} {C} φ u a) ≡ fst (unsafeComp Z φ u a)
    test-compR-1 = refl

    test-compR-2 : snd (compR {A = A} {B} {C} φ u a) ≡ snd (unsafeComp Z φ u a)
    test-compR-2 = refl

    test-compR-3 : trd (compR {A = A} {B} {C} φ u a) ≡ trd (unsafeComp Z φ u a)
    test-compR-3 = refl

module Univ (c : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ _ ] T ≃ A)) where
  univ : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
  univ {A = A} {B = B} eq i = let ((T , ev) , p) = c B
                               in fst (contrIsProp (c B)(A , eq)(B , idEquiv) i)

module _ {ℓ} {A : Set ℓ} {φ : I} {T : Partial (Set ℓ) φ}
             {f : PartialP φ (λ o → T o → A)}
             {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} where
  test-Glue-β : (t : PartialP φ T) (a : A) →
    unglue {A = A} {φ = φ} {T = T} {f} {pf} (unsafeGlue t a) ≡ a
  test-Glue-β _ _ = refl

  test-Glue-η : (b : primGlue A φ T f pf) →
    (glue {φ = φ} (λ{ (φ = i1) → b }) (unglue {φ = φ} b)) ≡ b
  test-Glue-η b = refl

module _ {ℓ} {A : Set ℓ} (let φ = i1) {T : Partial (Set ℓ) φ}
             {f : PartialP φ (λ o → T o → A)}
             {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} where
  test-unglue-0 : (b : primGlue A φ T f pf) →
    unglue {A = A} {φ = φ} {T = T} {f} {pf} b ≡ f itIsOne b
  test-unglue-0 _ = refl

  test-unglue-2 : (t : PartialP φ T) (a : A) →
    unglue {A = A} {φ = φ} {T = T} {f} {pf}
    (unsafeGlue {A = A}{φ = φ}{T = T}{f}{pf} t a) ≡ f itIsOne (t itIsOne) -- = a
  test-unglue-2 _ _ = refl

  test-glue-0 : (t : PartialP φ T) (a : A) →
    (unsafeGlue {A = A} {T = T} {f} {pf} t a) ≡ t itIsOne
  test-glue-0 _ _ = refl

module _ {ℓ} {A : Set ℓ} (w : Σ[ T ∈ Set ℓ ] T ≃ A) where
  T = fst w

  f : T → A
  f = fst (snd w)

  inv : A → T
  inv b = fst (fst (snd (snd (w)) b))

  id=f-inv : (b : A) → b ≡ f (inv b)
  id=f-inv b = snd (fst (snd (snd (w)) b))

  foo : (b : A) → (v : Σ[ x ∈ T ] b ≡ f x) → inv b ≡ fst v
  foo b v j = fst ((snd (snd (snd (w)) b)) v j)

  bar : (b : A) → (v : Σ[ x ∈ T ] b ≡ fst (snd w) x) → I → I → A
  bar b v j k = (snd (snd (snd (snd w) b) v j) k )

unglueEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I) (T : Partial (Set ℓ) φ)
  (f : PartialP φ λ o → (T o) ≃ A) → (Glue A φ T f) ≃ A
unglueEquiv A φ T f = unglue {φ = φ} , (λ b →
  let u = (λ j → (λ{ (φ = i1) → snd (fst (snd (snd (w itIsOne)) b)) j })) in
  ((glue {φ = φ} ((λ{ (φ = i1) → fst (fst (snd (snd (w itIsOne)) b)) }))
    (primComp (λ _ → A) φ u b)) , (λ k → fill (λ v → A) φ u b k))
  , (λ v j → let
      u' = (λ k →
        [ φ   ↦ (λ{ (φ = i1) → (snd (snd (snd (snd (w itIsOne)) b) v j) k ) }) , _ ↦
        [ ~ j ↦ (λ{ (j = i0) → fill (λ _ → A) φ u b k })
        , j   ↦ (λ{ (j = i1) → (snd v)  k }) ] ]) in
    (glue {φ = φ} (λ{ (φ = i1) → fst ((snd (snd (snd (w itIsOne)) b)) v j) })
      (primComp (λ _ → A) _ u' b))
    , ((λ z → fill (λ _ → A) _ u' b z))))
    where w : PartialP φ λ _ → Σ[ T ∈ _ ] T ≃ A
          w = λ o → (T o , f o)


EquivContr : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ _ ] T ≃ A)
EquivContr A = (A , idEquiv) , (λ w i →
  let φ = (~ i ∨ i)
      Tf : Partial (Σ[ T ∈ _ ] T ≃ A) (~ i ∨ i)
      Tf = [ ~ i ↦ (λ{ (i = i0) → A , idEquiv }) , i ↦ (λ{ (i = i1) → w }) ]
   in Glue A φ (λ o → fst (Tf o)) (λ o → snd (Tf o))
     , unglueEquiv A φ (λ o → fst (Tf o)) (λ o → snd (Tf o)))

univ : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
univ = Univ.univ EquivContr

eqToPath : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
eqToPath {ℓ} {A} {B} f = λ i → Glue B (~ i ∨ i)
  ([ ~ i ↦ (λ _ → A) , i ↦ (λ _ → B) ])
  ([ ~ i ↦ (λ{ (i = i0) → f }) , i ↦ (λ{ (i = i1) → pathToEquiv (λ _ → B) }) ])

not : Bool → Bool
not true = false
not false = true

notnot : ∀ y → y ≡ not (not y)
notnot true = refl
notnot false = refl

Σ-path : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {x y : A} (p : x ≡ y)
  {bx : B x} {by : B y} → PathP (λ i → B (p i)) bx by
                        → _≡_ {A = Σ A B} (x , bx) (y , by)
Σ-path pa pb = λ i → (pa i) , pb i

nothelp : ∀ y (y₁ : Σ[ x ∈ Bool ] (y ≡ not x)) → (not y , notnot y) ≡ y₁
nothelp y (true  , eq) = pathJ (λ y₁ eq' →
  (not y₁ , notnot y₁) ≡ (true  , sym eq')) refl _ (sym eq)
nothelp y (false , eq) = pathJ (λ y₁ eq' →
  (not y₁ , notnot y₁) ≡ (false , sym eq')) refl _ (sym eq)

notEquiv : Bool ≃ Bool
notEquiv = not , (λ { y → (not y , notnot y) , nothelp y })

test : Bool
test = primComp (λ i → univ {A = Bool} {B = Bool} notEquiv i)
                i0 (λ _ → empty) true


test-test : test ≡ unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                   false))))))))
test-test = refl


test-test2 : test ≡ false
test-test2 = refl

test2 : Bool
test2 = primComp (λ i → eqToPath {A = Bool} {B = Bool} notEquiv i)
                 i0
                 (λ _ → empty)
                 true


test2-test : test2 ≡ unsafeComp (λ _ → Bool) i0 (λ _ _ → false)
                    (unsafeComp (λ _ → Bool) i0 ((λ _ _ → false))
                    (unsafeComp (λ _ → Bool) i0 ((λ _ _ → false))
                    (unsafeComp (λ _ → Bool) i0 ((λ _ _ → false))
                     false)))
test2-test = refl

test3 : Bool
test3 = primComp (λ i → equivToPath {A = Bool} {B = Bool} notEquiv i)
                 i0
                 (λ _ → empty)
                 true


test3-test : test3 ≡ unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                    (unsafeComp (λ _ → Bool) i0 (λ _ _ → false)
                    (unsafeComp (λ i → Bool) i0 (λ _ _ → false)
                     false))
test3-test = refl

data D2 (A : Set) : Set where
   c1 : D2 A
   c2 : D2 A

test5-test : ∀ j →  primComp (λ i → D2 Bool) (j ∨ ~ j)
  (λ i → [ j ↦ (λ{ (j = i1) → c1 }) , ~ j ↦ (λ{ (j = i0) → c1 }) ]) c1 ≡ c1
test5-test j = refl

test6-test : (j : I → I) → primComp (λ i → D2 Bool) (j i0) (λ i o → c1) c1 ≡ c1
test6-test j = refl

test4-test : ∀ j → primComp (λ i → Bool) (j ∨ ~ j)
  (λ i → [ j ↦ (λ{ (j = i1) → false }) , ~ j ↦ (λ{ (j = i0) → false }) ] ) false ≡ false
test4-test j = refl


data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 20 _∷_

ListNot : List Bool ≡ List Bool
ListNot = λ i → List (univ {A = Bool} {B = Bool} notEquiv i)

trues : List Bool
trues = true ∷ true ∷ []

falses : List Bool
falses = primComp (λ i → ListNot i) i0 (λ _ → empty) trues

test-falses : falses ≡ (false ∷ false ∷ [])
test-falses = refl

trues2 : List Bool
trues2 = primComp (λ i → trans ListNot ListNot i) i0 (λ _ → empty) trues

test-trues2 : trues2 ≡ trues
test-trues2 = refl

trues3 : List Bool
trues3 = primComp (λ i → let p = trans ListNot ListNot in
                         trans p p i)
                  i0
                  (λ _ → empty)
                  trues

test-trues3 : trues3 ≡ trues
test-trues3 = refl
