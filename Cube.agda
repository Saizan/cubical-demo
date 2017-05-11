{-# OPTIONS --cubical #-}
module Cube where


open import Primitives public
open import Level
open import Data.Product public using (Σ; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Bool using (Bool; true; false)
open import PathPrelude


test-sym : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → sym (sym p) ≡ p
test-sym p = refl


testBool : (p : Path true false) → Bool
testBool p = primComp (\ _ → Bool) i1 (\ j → \ _ → p j) true
-- cannot reduce to true, because it's already reducing to false.


eta-expand : ∀ {a} {A : Set a} {x y : A} → (p : Path x y) -> Path x y
eta-expand p = λ z → p z

eta-eq : ∀ {a} {A : Set a} {x y : A} → (p : Path x y) -> Path p (eta-expand p)
eta-eq p = refl


module IntervalEquations where
  postulate
    P : I -> Set
  test0 : (P (~ i0) ≡ P i1)
  test0 = refl
  test1 : P (~ i1) ≡ P i0
  test1 = refl
  test2 : ∀ {i j} → P (~ (i ∧ j)) ≡ P (~ i ∨ ~ j)
  test2 = refl
  test3 : ∀ {i j} → P (~ (i ∨ j)) ≡ P (~ i ∧ ~ j)
  test3 = refl
  test4 : ∀ {i} → P (~ (~ i)) ≡ P i
  test4 = refl

  test5 : ∀ {i} → P (_∧_ i0 i) ≡ P i0
  test5 = refl

  test52 : ∀ {i} → P (_∧_ i i) ≡ P i
  test52 = refl

  test53 : ∀ {i j} → P (i ∧ j) ≡ P (j ∧ i)
  test53 = refl

  testn6 : ∀ {i} → P (i1 ∧ i) ≡ P i
  testn6 = refl

  testn7 : ∀ {i} → P (i ∧ i0) ≡ P i0
  testn7 = refl

  testn8 : ∀ {i} → P (i ∧ i1) ≡ P i
  testn8 = refl




J-comp : ∀ {a}{p}{A : Set a}{x : A} → {P : ∀ y → Id x y → Set p} → (d : P x reflId)
         → J P d reflId ≡ d
J-comp _ = refl




outPartial : ∀ {a} {A : Set a} → Partial A i1 → A
outPartial = \ f → f itIsOne

inPartial : ∀ {a} {A : Set a} → A → Partial A i1
inPartial a = \ _ → a




compPi : ∀ {a b} {A : I -> Set a}{B : ∀ i → A i → Set b} →
          (let a = _; C : I → Set a; C = \ i → (x : A i) → B i x) (φ : I) → (∀ i → Partial (C i) φ) → (a : C i0) → C i1
compPi {A = A} {B = B} φ u a x1 = unsafeComp (\ i → B i (v i)) φ (λ i → \ o → u i o (v i)) (a (v i0))
  where
    v : (i : I) → A i
    v = λ i → unsafeComp (λ j → A (i ∨ (~ j))) i (λ j → p[_] {A = A} x1 _ (~ j) ) x1
    f : ∀ i → (a : A i) → Partial (B i a) φ
    f i a = \ { _ → u i itIsOne a  }


compPi' : ∀ {a b} → ∀ {A : I -> Set a}{B : ∀ i → A i → Set b} →
            (let a = _; C : I → Set a; C = \ i → (x : A i) → B i x) (φ : I) → (∀ i → Partial (C i) φ) → (a : C i0) → C i1
compPi' {A = A} {B = B} φ u a = unsafeComp C φ u a
     where
      C = \ i → (x : A i) → B i x

test-compPi : ∀ {a b} → ∀ {A : I -> Set a}{B : ∀ i → A i → Set b} →
            (let a = _; C : I → Set a; C = \ i → (x : A i) → B i x) (φ : I)
            → (u : ∀ i → Partial (C i) φ) → (a : C i0) →
            compPi {A = A} {B} φ u a ≡ compPi' {A = A} {B} φ u a
test-compPi = λ φ p p0 → refl

compPath : ∀ {a} → {A : I → Set a} → (u v : ∀ i → A i) (φ : I) (let C = \ (i : I) → Path (u i) (v i))
              (p : ∀ i → Partial (C i) φ) → C i0 → C i1
compPath {A = A} u v φ p p0 = \ j → unsafeComp A (φ ∨ (~ j ∨ j))
                                                (λ i → [ φ   ↦ (\ o → (p i o) j) , (~ j ∨ j) ↦
                                                       [ ~ j ↦ (\ _ → u i)
                                                       , j   ↦ (\ _ → v i) ]
                                                       ])
                                                (p0 j)

compPath' : ∀ {a} → {A : I → Set a} → (u v : ∀ i → A i) (φ : I) (let C = \ (i : I) → Path (u i) (v i))
              (p : ∀ i → Partial (C i) φ) → C i0 → C i1
compPath' {A = A} u v = unsafeComp C
  where C = \ (i : I) → Path (u i) (v i)

test-compPath : ∀ {a} → {A : I → Set a} → (u v : ∀ i → A i) (φ : I) (let C = \ (i : I) → Path (u i) (v i))
              (p : ∀ i → Partial (C i) φ) → (p0 : C i0) → compPath u v φ p p0 ≡ compPath' u v φ p p0
test-compPath = λ u v φ p p0 → refl


module TestPathP {a} {A : I → I → Set a} (u : ∀ i → A i i0)(v : ∀ i → A i i1)
                  (φ : I) (let C = \ (i : I) → PathP (A i) (u i) (v i))
                  (p : ∀ i → Partial (C i) φ) (p0 : C i0) where

 compPathP : C i1
 compPathP = \ j → unsafeComp (\ i → A i j) (φ ∨ (~ j ∨ j))
                                                (λ i → [ φ   ↦ (\ o → (p i o) j) , (~ j ∨ j) ↦
                                                       [ ~ j ↦ (\ { _ → u i } )
                                                       , j   ↦ (\ { _ → v i } ) ]
                                                       ])
                                                (p0 j)

 compPathP' : C i1
 compPathP' = unsafeComp C φ p p0

 test-compPathP : compPathP ≡ compPathP'
 test-compPathP = refl

module RecordComp where
  record R {a b} (A : Set a) (B : A -> Set b) (C : (x : A) → B x → Set a) : Set (a ⊔ b) where
     coinductive
     constructor _,_
     field
       fst : A
       snd : B fst
       trd : C fst snd
  open R


  {-# TERMINATING #-}
  compR : ∀ {a b} {A : I -> Set a}{B : ∀ i → A i → Set b}{C : ∀ i → (x : A i) → B i x → Set a} →
              (let a = _; Z : I → Set a; Z = \ i → R (A i) (B i) (C i)) (φ : I) → (∀ i → Partial (Z i) φ) → (a : Z i0) → Z i1
  fst (compR {A = A} {B} φ w w0) = unsafeComp A φ (λ i →  (\{_ → fst (w i itIsOne) }) ) (fst w0)
  snd (compR {A = A} {B} φ w w0) = unsafeComp (\ i → B i (a i)) φ (λ i → (\{_ → snd (w i itIsOne) })) (snd w0)
    where
      a = fill (λ z → A z) φ (\ i →  (\{_ → fst (w i itIsOne) }) ) (fst w0)
  trd (compR {A = A} {B} {C} φ w w0) = unsafeComp (\ i → C i (a i) (b i)) φ ((λ i →  (\{_ → trd (w i itIsOne) })  )) (trd w0)

    where
      Z : I → Set _
      Z = \ i → R (A i) (B i) (C i)
      z : (i : I) -> _
      z = \ i → compR {A = \ j → A (i ∧ j)} {\ j → B (i ∧ j)} {\ j → C (i ∧ j)} (φ ∨ ~ i)
                      (\ j → unsafePOr {_} φ (~ i) {λ _ → R (A (i ∧ j)) (B (i ∧ j)) (C (i ∧ j))} (w (i ∧ j)) (\{_ → w0 })) w0
      ---fill Z φ w w0
      a : (i : I) → _
      a = \ i → fst (z i)
      b : (i : I) -> _
      b = \ i → snd (z i)

  compR-test : ∀ {a b} {A : I -> Set a}{B : ∀ i → A i → Set b}{C : ∀ i → (x : A i) → B i x → Set a} →
              (let a = _; Z : I → Set a; Z = \ i → R (A i) (B i) (C i)) (φ : I) → (u : ∀ i → Partial (Z i) φ)
              → (a : Z i0) →
              Path (fst (compR {A = A} {B} {C} φ u a)) (fst (unsafeComp Z φ u a))
  compR-test φ u a = refl

  compR-test1 : ∀ {a b} {A : I -> Set a}{B : ∀ i → A i → Set b}{C : ∀ i → (x : A i) → B i x → Set a} →
              (let a = _; Z : I → Set a; Z = \ i → R (A i) (B i) (C i)) (φ : I) → (u : ∀ i → Partial (Z i) φ) → (a : Z i0) →
              Path (snd (compR {A = A} {B} {C} φ u a)) (snd (unsafeComp Z φ u a))
  compR-test1 φ u a = refl

  compR-test2 : ∀ {a b} {A : I -> Set a}{B : ∀ i → A i → Set b}{C : ∀ i → (x : A i) → B i x → Set a} →
              (let a = _; Z : I → Set a; Z = \ i → R (A i) (B i) (C i)) (φ : I) → (u : ∀ i → Partial (Z i) φ) → (a : Z i0) →
              Path (trd (compR {A = A} {B} {C} φ u a)) (trd (unsafeComp Z φ u a))
  compR-test2 φ u a = refl









module Univ (c : ∀ {a} (A : Set a) → Contr.isContr (Σ _ \ T → Equiv T A)) where


  univ : ∀ {l} {A B : Set l} → Equiv A B → Path A B
  univ {A = A} {B = B} eq = let ((T , ev) , p) = c B in \ i → fst (Contr.isContrProp (c B) (A , eq) (B , idEquiv) i)






test-unglue0 : ∀ {l} {A : Set l} (let φ = i1) {T : Partial (Set l) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                  (b : primGlue A φ T f pf) → unglue {A = A} {φ = φ} {T = T} {f} {pf} b ≡ f itIsOne b
test-unglue0 _ = refl

test-Glue-beta : ∀ {l} {A : Set l} {φ : I} {T : Partial (Set l) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                  (t : PartialP φ T) (a : A) → unglue {A = A} {φ = φ} {T = T} {f} {pf} (unsafeGlue t a) ≡ a
test-Glue-beta _ _ = refl

test-Glue-eta : ∀ {l} {A : Set l} {φ} {T : Partial (Set l) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                  (b : primGlue A φ T f pf) → (glue {φ = φ} (\{_ → b }) (unglue {φ = φ} b)) ≡ b
test-Glue-eta b = refl

test-unglue2 : ∀ {l} {A : Set l} (let φ = i1)  {T : Partial (Set l) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                  (t : PartialP φ T) (a : A) → unglue {A = A} {φ = φ} {T = T} {f} {pf} (unsafeGlue {A = A} {φ = φ} {T = T} {f} {pf} t a)
                                               ≡ f itIsOne (t itIsOne) -- = a
test-unglue2 _ _ = refl

test-glue0 : ∀ {l} {A : Set l} (let φ = i1) {T : Partial (Set l) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                  (t : PartialP φ T) (a : A) → (unsafeGlue {A = A} {T = T} {f} {pf} t a) ≡ t itIsOne
test-glue0 _ _ = refl

coe : ∀ {l} {A : Set l} → (w : Σ (Set l) \ T → Equiv T A) → fst w → A
coe (_ , (f , _)) = f

inv : ∀ {l} {A : Set l} → (w : Σ (Set l) \ T → Equiv T A) → A → fst w
inv w = \ b → fst (fst (snd (snd (w)) b))

id=coeinv : ∀ {l} {A : Set l} → (w : Σ _ \ T → Equiv T A) → (b : A) → Path b (coe w (inv w b))
id=coeinv w = \ b → snd (fst (snd (snd (w)) b))

foo : ∀ {l} {A : Set l} → (w : Σ _ \ T → Equiv T A) → (b : A) → (v : Σ (fst w) (λ x → b ≡ coe w x))
                   -> Path (inv w b) (fst v)
foo w b v = \ j → fst ((snd (snd (snd (w)) b)) v j)

bar : ∀ {l} {A : Set l} → (w : Σ (Set l) \ T → Equiv T A) → (b : A) → (v : Σ (fst w) (λ x → b ≡ fst (snd w) x)) -> (j k : I) -> A
bar w b v = \ j → \ k → (snd (snd (snd (snd w) b) v j) k )

unglue-equiv : ∀ {a} (A : Set a) → (φ : I) → (T : Partial (Set a) φ) (f : PartialP φ \ o → Equiv (T o) A)  → Equiv (Glue A φ T f) A
unglue-equiv A φ T f = unglue {φ = φ} , (λ b → ((glue {φ = φ} ((\{_ → fst (fst (snd (snd (w itIsOne)) b)) }))
                                                               (primComp (\ _ → A) φ (\ j → (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b))
                                                           , (\ k → fill (λ v → A) φ (\ j → (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b k))
                                                  , (λ v → \ j →
                                                      (glue {φ = φ} (\{_ → fst ((snd (snd (snd (w itIsOne)) b)) v j) })
                                                        (primComp (λ _ → A) _ (\ k → [ φ   ↦ (\{_ → (snd (snd (snd (snd (w itIsOne)) b) v j) k ) }) , _ ↦
                                                                                     [ ~ j ↦ (\{_ → fill (λ _ → A) φ (\ j →
                                                                                                     (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b k })
                                                                                     , j   ↦ (\{_ → snd v k }) ] ])
                                                                              b))
                                                      , ( (\ z -> fill (\ _ → A) _ (\ k →
                                                                       [ φ   ↦ (\{_ → (snd (snd (snd (snd (w itIsOne)) b) v j) k ) }) , _ ↦
                                                                       [ ~ j ↦ (\{_ → fill (λ _ → A) φ (\ j →
                                                                                       (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b k })
                                                                       , j   ↦ (\{_ → (snd v)  k }) ] ])
                                                                       b
                                                                       z) )))
   where w : PartialP φ \ _ → Σ _ \ T → Equiv T A
         w = \ o → (T o , f o)


Equiv-contr : ∀ {a} (A : Set a) → Contr.isContr (Σ _ \ T → Equiv T A)
Equiv-contr A = (A , idEquiv) , (λ w →  \ i → let φ = (~ i ∨ i)
                                                  Tf : Partial (Σ _ \ T → Equiv T A) (~ i ∨ i)
                                                  Tf = [ ~ i ↦ (\{_ → A , idEquiv }) , i ↦ (\{_ → w }) ]
                                              in Glue A φ (\ o → fst (Tf o)) (\ o → snd (Tf o))
                                                 , unglue-equiv A φ (\ o → fst (Tf o)) (\ o → snd (Tf o)))

univ : ∀ {l} {A B : Set l} → Equiv A B → Path A B
univ = Univ.univ Equiv-contr


eqToPath : ∀ {l} {A B : Set l} → Equiv A B → Path A B
eqToPath {l} {A} {B} f = \ i → Glue B (~ i ∨ i) ([ ~ i ↦ (\ _ → A) , i ↦ (\ _ → B) ]) ([ ~ i ↦ (\{_ → f }) , i ↦ (\{_ → pathToEquiv (\ _ → B) }) ])


not : Bool → Bool
not true = false
not false = true

notnot : ∀ y → y ≡ not (not y)
notnot true = refl
notnot false = refl

Σ-path : ∀ {a b} {A : Set a} {B : A → Set b} → {x y : A} → (p : Path x y) → {bx : B x} {by : B y} → PathP (\ i → B (p i)) bx by
           → Path {A = Σ A B} (x , bx) (y , by)
Σ-path pa pb = \ i → (pa i) , primPathPApply pb i

nothelp : ∀ y (y₁ : Σ Bool (λ x → Path y (not x))) →
          Path (not y , notnot y) y₁
nothelp y (true , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (true , sym eq')) refl _ (sym eq)
nothelp y (false , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (false , sym eq')) refl _ (sym eq)

notEquiv : Equiv Bool Bool
notEquiv = not , (\ { y → (not y , notnot y) , nothelp y })

test : Bool
test = primComp (\ i → univ {A = Bool} {B = Bool} notEquiv i)
                i0 (\ _ → empty) true


test-test : test ≡ unsafeComp (\ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (\ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (\ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (\ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (\ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (\ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (\ _ _ → false)
                  (unsafeComp (λ i → Bool) i0 (\ _ _ → false)
                   false))))))))
test-test = refl


test-test2 : test ≡ false
test-test2 = refl

test2 : Bool
test2 = primComp (\ i → eqToPath {A = Bool} {B = Bool} notEquiv i)
                 i0
                 (\ _ → empty)
                 true


test2-test : test2 ≡ unsafeComp (λ _ → Bool) i0 (\ _ _ → false)
                    (unsafeComp (λ _ → Bool) i0 ((\ _ _ → false))
                    (unsafeComp (λ _ → Bool) i0 ((\ _ _ → false))
                    (unsafeComp (λ _ → Bool) i0 ((\ _ _ → false))
                     false)))
test2-test = refl

test3 : Bool
test3 = primComp (\ i → eqToPath' {A = Bool} {B = Bool} notEquiv i)
                 i0
                 (\ _ → empty)
                 true


test3-test : test3 ≡ unsafeComp (λ i → Bool) i0 (\ _ _ → false)
                    (unsafeComp (λ _ → Bool) i0 (\ _ _ → false)
                    (unsafeComp (λ i → Bool) i0 (\ _ _ → false)
                     false))
test3-test = refl

data D2 (A : Set) : Set where
   c1 : D2 A
   c2 : D2 A

test05-test : ∀ j → primComp (\ i → D2 Bool) ( (j ∨ ~ j) ) (\ i → [ j ↦ (\{_ → c1 }) , ~ j ↦ (\{_ → c1 }) ]) c1 ≡ c1
test05-test j = refl

test5-test : ∀ j → primComp (\ i → D2 Bool) (j ∨ ~ j) (\ i → [ j ↦ (\{_ → c1 }) , ~ j ↦ (\{_ → c1 }) ]) c1 ≡ c1
test5-test j = refl

test6-test : ∀ (j : I -> I) → primComp (\ i → D2 Bool) (j i0) (\ i → \ o → c1) c1 ≡ c1
test6-test j = refl

test4-test : ∀ j → primComp (\ i → Bool) (j ∨ ~ j) (\ i → [ j ↦ (\{_ → false }) , ~ j ↦ (\{_ → false }) ] ) false ≡ false
test4-test j = refl


data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 20 _∷_

ListNot : List Bool ≡ List Bool
ListNot = \ i → List (univ {A = Bool} {B = Bool} notEquiv i)

trues : List Bool
trues = true ∷ true ∷ []

falses : List Bool
falses = primComp (\ i → ListNot i) i0 (\ _ → empty) trues

test-falses : falses ≡ (false ∷ false ∷ [])
test-falses = refl

trues2 : List Bool
trues2 = primComp (\ i → trans ListNot ListNot i) i0 (\ _ → empty) trues

test-trues2 : trues2 ≡ trues
test-trues2 = refl

trues3 : List Bool
trues3 = primComp (\ i → let p = trans ListNot ListNot in
                         trans p p i)
                  i0
                  (\ _ → empty)
                  trues

test-trues3 : trues3 ≡ trues
test-trues3 = refl
