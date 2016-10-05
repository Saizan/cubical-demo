{-# OPTIONS --cubical #-}
module Cube where

open import Primitives public
open import Level

record Σ {a b} (A : Set a) (B : A -> Set b) : Set (a ⊔ b) where
   constructor _,_
   field
     fst : A
     snd : B fst

open Σ public

-- We redefine Bool here because so far only datatypes define while
-- the right primitives have been bound get a comp that reduces.
data Bool : Set where
  true false : Bool

refl : ∀ {a} {A : Set a} {x : A} → Path x x
refl {x = x} = λ i → x

sym : ∀ {a} {A : Set a} → {x y : A} → Path x y → Path y x
sym p = \ i → p ∙ (~ i)

test-sym : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → sym (sym p) ≡ p
test-sym p = refl

trans : ∀ {a} {A : Set a} → {x y z : A} → Path x y → Path y z → Path x z
trans {A = A} {x} {y} p q = \ i → primComp (λ j → A) _ {- (i ∨ ~ i) -}
                                           (\ j → [ i     ↦ r[ q j ]
                                                  , (~ i) ↦  r[ x ]  ])
                                           (p ∙ i)

testBool : (p : Path true false) → Bool
testBool p = primComp (\ _ → Bool) i1 (\ j → r[ p j ]) true
-- cannot reduce to true, because it's already reducing to false.


fun-ext : ∀ {a b} {A : Set a} {B : A → Set b} → {f g : (x : A) → B x}
          → (∀ x → Path (f x) (g x)) → Path f g
fun-ext p = λ i x → p x i

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

  -- test52 : ∀ {i} → P (_∧_ i i) ≡ P i
  -- test52 = refl

  -- test53 : ∀ {i j} → P (i ∧ j) ≡ P (j ∧ i)
  -- test53 = refl

  testn6 : ∀ {i} → P (i1 ∧ i) ≡ P i
  testn6 = refl

  testn7 : ∀ {i} → P (i ∧ i0) ≡ P i0
  testn7 = refl

  testn8 : ∀ {i} → P (i ∧ i1) ≡ P i
  testn8 = refl




reflId : ∀ {a} {A : Set a}{x : A} → Id x x
reflId {x = x} = conid i1 (λ _ → x)

fromPath : ∀ {A : Set}{x y : A} → Path x y -> Id x y
fromPath p = conid i0 p

transId : ∀ {a} {A : Set a} → {x y z : A} → Id x y → Id y z → Id x z
transId {A = A} {x} {y} p = J (λ y _ → Id x y) p

congId :  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → ∀ {x y} → Id x y → Id (f x) (f y)
congId f {x} {y} = J (λ y _ → Id (f x) (f y)) reflId

J-comp : ∀ {a}{p}{A : Set a}{x : A} → {P : ∀ y → Id x y → Set p} → (d : P x reflId)
         → J P d reflId ≡ d
J-comp _ = refl




outPartial : ∀ {a} {A : Set a} → Partial A i1 → A
outPartial = \ f → f itIsOne

inPartial : ∀ {a} {A : Set a} → A → Partial A i1
inPartial a = \ _ → a


fill : ∀ {a : I -> Level} (A : (i : I) → Set (a i)) (φ : I) → ((i : I) → Partial (A i) φ) → A i0 → (i : I) → A i
fill A φ u a0 i = unsafeComp (\ j → A (i ∧ j)) (φ ∨ ~ i) (\ j → unsafePOr φ (~ i) (u (i ∧ j)) r[ a0 ]) a0


compPi : ∀ {a b} {A : I -> Set a}{B : ∀ i → A i → Set b} →
          (let a = _; C : I → Set a; C = \ i → (x : A i) → B i x) (φ : I) → (∀ i → Partial (C i) φ) → (a : C i0) → C i1
compPi {A = A} {B = B} φ u a x1 = unsafeComp (\ i → B i (v i)) φ (λ i → \ o → u i o (v i)) (a (v i0))
  where
    v : (i : I) → A i
    v = λ i → unsafeComp (λ j → A (i ∨ (~ j))) i (λ j → p[_] {A = A} x1 _ (~ j) ) x1
    f : ∀ i → (a : A i) → Partial (B i a) φ
    f i a = r[ u i itIsOne a  ]


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
  fst (compR {A = A} {B} φ w w0) = unsafeComp A φ (λ i → r[ fst (w i itIsOne) ]) (fst w0)
  snd (compR {A = A} {B} φ w w0) = unsafeComp (\ i → B i (a i)) φ (λ i → r[ snd (w i itIsOne) ] ) (snd w0) --
    where
      a = fill (λ z → A z) φ (\ i → r[ fst (w i itIsOne) ]) (fst w0)
  trd (compR {A = A} {B} {C} φ w w0) = unsafeComp (\ i → C i (a i) (b i)) φ ((λ i → r[ trd (w i itIsOne) ] )) (trd w0)

    where
      Z : I → Set _
      Z = \ i → R (A i) (B i) (C i)
      z : (i : I) -> _
      z = \ i → compR {A = \ j → A (i ∧ j)} {\ j → B (i ∧ j)} {\ j → C (i ∧ j)} (φ ∨ ~ i)
                      (\ j → unsafePOr {_} φ (~ i) {λ _ → R (A (i ∧ j)) (B (i ∧ j)) (C (i ∧ j))} (w (i ∧ j)) r[ w0 ]) w0
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



singl : ∀ {l} {A : Set l} (a : A) -> Set l
singl {A = A} a = Σ A (\ x → a ≡ x)

contrSingl : ∀ {l} {A : Set l} {a b : A} (p : a ≡ b) → Path {A = singl a} (a , refl) (b , p)
contrSingl p = \ i → ((p i) , \ j →  p (i ∧ j))

pathJ : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Path x y → Set p) → P x ((\ i -> x)) → ∀ {y} (p : Path x y) → P y p
pathJ P d p = primComp (λ i → let x , y = contrSingl p ∙ i in P x y) i0 (\ _ → empty) d

module Contr where

  isContr : ∀ {a} → (A : Set a) → Set a
  isContr A = Σ A (\ x → ∀ y → x ≡ y)

  contr : ∀ {a} {A : Set a} → isContr A → (φ : I) → (u : Partial A φ) → A
  contr {A = A} (c , p) φ u = primComp (\ _ → A) φ (λ i → \ o → p (u o) ∙ i) c

  lemma : ∀ {a} {A : Set a}
          → (contr1 : ∀ φ → Partial A φ → A)
          → (contr2 : ∀ u → u ≡ (contr1 i1 r[ u ]))
          → isContr A
  lemma {A = A} contr1 contr2 = x , (λ y → let module M = R y in trans (contr2 x) (trans (\ i → M.v i) (sym (contr2 y)))) where
        x = contr1 i0 empty
        module R (y : A) (i : I) where
          φ = ~ i ∨ i
          u : Partial A φ
          u = primPOr (~ i) i r[ x ] r[ y ]
          v = contr1 φ u

  isContrProp : ∀ {a} {A : Set a} (h : isContr A) -> ∀ (x y : A) → x ≡ y
  isContrProp {A = A} h a b = \ i → primComp (\ _ → A) _ (\ j → [ (~ i) ↦ r[ snd h a j ] , i ↦ r[ snd h b ∙ j ] ]) (fst h)

module Pres {la lb : I → _} {T : (i : I) → Set (lb i)}{A : (i : I) → Set (la i)} (f : ∀ i → T i → A i) (φ : I) (t : ∀ i → Partial (T i) φ)
                (t0 : T i0 {- [ φ ↦ t i0 ] -}) where

 c1 c2 : A i1
 c1 = unsafeComp A φ (λ i → r[ f i (outPartial (t i)) ]) (f i0 t0)
 c2 = f i1 (unsafeComp T φ t t0)

 a0 = f i0 t0

 a : ∀ i → Partial (A i) φ
 a i = r[ f i (outPartial (t i)) ]

 u : ∀ i → A i
 u = fill A φ a a0

 v : ∀ i → T i
 v = fill T φ t t0

 pres : Path c1 c2
 pres = \ j → unsafeComp A (φ ∨ (j ∨ ~ j)) (λ i → primPOr φ ((j ∨ ~ j)) (a i) (primPOr j (~ j)  r[  f i (v i)  ] r[  u i  ])) a0


module Equiv {l l'} (A : Set l)(B : Set l') where
  isEquiv : (A -> B) → Set (l' ⊔ l)
  isEquiv f = ∀ y → Contr.isContr (Σ A \ x → y ≡ f x)

  Equiv = Σ _ isEquiv

  equiv : (f : Equiv) → ∀ φ (t : Partial A φ) (a : B {- [ φ ↦ f t ] -}) → PartialP φ (\ o → Path a (fst f (t o)))
           -> Σ A \ x → a ≡ fst f x -- [ φ ↦ (t , \ j → a) ]
  equiv (f , [f]) φ t a p = Contr.contr ([f] a) φ \ o → t o , (\ i → p o i)

  equiv1 : (f : Equiv) → ∀ φ (t : Partial A φ) (a : B {- [ φ ↦ f t ] -}) → PartialP φ (\ o → Path a (fst f (t o))) -> A
  equiv1 f φ t a p = fst (equiv f φ t a p)

  equiv2 : (f : Equiv) → ∀ φ (t : Partial A φ) (a : B {- [ φ ↦ f t ] -}) → (p : PartialP φ (\ o → Path a (fst f (t o))))
           → a ≡ fst f (equiv1 f φ t a p)
  equiv2 f φ t a p = snd (equiv f φ t a p)

open Equiv public

idEquiv : ∀ {a} {A : Set a} → Equiv A A
idEquiv = (λ x → x) , (λ y → (y , refl) , (λ y₁ → contrSingl (snd y₁)))


module Univ (c : ∀ {a} (A : Set a) → Contr.isContr (Σ _ \ T → Equiv T A)) where


  univ : ∀ {l} {A B : Set l} → Equiv A B → Path A B
  univ {A = A} {B = B} eq = let ((T , ev) , p) = c B in \ i → fst (Contr.isContrProp (c B) (A , eq) (B , idEquiv) ∙ i)


{-# BUILTIN ISEQUIV isEquiv #-}


pathToEquiv : ∀ {l : I → _} (E : (i : I) → Set (l i)) → Equiv (E i0) (E i1)
pathToEquiv E = f
              , (λ y → (g y
                       , (\ j → primComp E (~ j ∨ j) (\ i → [ ~ j ↦  r[ v i y ]  , j ↦  r[ u i (g y) ]  ]) (g y))) ,
                                        prop-f-image y _ )
  where
    A = E i0
    B = E i1
    transp : ∀ {l : I → _} (E : (i : I) → Set (l i)) → E i0 → E i1
    transp E x = primComp E i0 (\ _ → empty) x
    f : A → B
    f = transp E
    g : B → A
    g = transp (\ i → E (~ i))
    u : (i : I) → A → E i
    u i x = fill E i0 (\ _ → empty) x i
    v : (i : I) → B → E i
    v i y = fill (\ i → E (~ i)) i0 (\ _ → empty) y (~ i)
    prop-f-image : (y : B) → (a b : Σ _ \ x → y ≡ f x) → a ≡ b
    prop-f-image y (x0 , b0) (x1 , b1) = \ k → (w k) , (\ j → d j k)
       where
         w0 = \ (j : I) → primComp (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  r[ v (~ i) y ]  , j ↦  r[ u (~ i) x0 ]  ])) (b0 ∙ j)
         w1 = \ (j : I) → primComp (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  r[ v (~ i) y ]  , j ↦  r[ u (~ i) x1 ]  ])) (b1 ∙ j)
         t0 = \ (j : I) → fill (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  r[ v (~ i) y ]  , j ↦  r[ u (~ i) x0 ]  ])) (b0 ∙ j)
         t1 = \ (j : I) → fill (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  r[ v (~ i) y ]  , j ↦  r[ u (~ i) x1 ]  ])) (b1 ∙ j)
         w = \ (k : I) → primComp (λ _ → A) (~ k ∨ k) (\ j → [ ~ k ↦ r[ w0 j ] , k ↦ r[ w1 j ] ]) (g y)
         t = \ (j k : I) → fill (λ _ → A) (~ k ∨ k) (\ j → [ ~ k ↦ r[ w0 j ] , k ↦ r[ w1 j ] ]) (g y) j
         d = \ (j k : I) → primComp E ((~ k ∨ k) ∨ (~ j ∨ j)) ((\ i → [ ~ k ∨ k ↦ [ ~ k ↦  r[  t0 j (~ i)  ]  , k ↦  r[ t1 j (~ i) ]  ]
                                                   , ~ j ∨ j ↦ [ ~ j ↦  r[ v (i) y ]  , j ↦  r[ u (i) (w k) ]  ] ])) (t j k)

pathToEquiv2 : ∀ {l : I → _} (E : (i : I) → Set (l i)) → _
pathToEquiv2 {l} E = snd (pathToEquiv E)

{-# BUILTIN PATHTOEQUIV pathToEquiv2 #-}

module GluePrims where
 primitive
  primGlue : ∀ {a b} (A : Set a) → ∀ φ → (T : Partial (Set b) φ) → (f : PartialP φ (λ o → T o → A))
                                         → (pf : PartialP φ (λ o → isEquiv (T o) A (f o))) → Set b
  prim^glue : ∀ {a b} {A : Set a} {φ : I} {T : Partial (Set b) φ}
                {f : PartialP φ (λ o → T o → A)}
                {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                PartialP φ T → A → primGlue A φ T f pf
  prim^unglue : ∀ {a b} {A : Set a} {φ : I} {T : Partial (Set b) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                  primGlue A φ T f pf → A

open GluePrims renaming (prim^glue to glue; prim^unglue to unglue)

module GluePrims' (dummy : Set₁) = GluePrims
open GluePrims' Set using () renaming (prim^glue to unsafeGlue)


Glue : ∀ {a b} (A : Set a) → ∀ φ → (T : Partial (Set b) φ) (f : (PartialP φ \ o → Equiv (T o) A))  → Set _
Glue A φ T f = primGlue A φ T (\ o → fst (f o)) (\ o → snd (f o))

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
                  (b : primGlue A φ T f pf) → (glue {φ = φ} r[ b ] (unglue {φ = φ} b)) ≡ b
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
fst (unglue-equiv A φ T f) = unglue {φ = φ}
snd (unglue-equiv {a} A φ T f) = (λ b → ((glue {φ = φ} (r[ fst (fst (snd (snd (w itIsOne)) b)) ])
                                                               (primComp (\ _ → A) φ (\ j → r[ snd (fst (snd (snd (w itIsOne)) b)) ∙ j ]) b))
                                                           , (\ k → fill (λ v → A) φ (\ j → r[ snd (fst (snd (snd (w itIsOne)) b)) ∙ j ]) b k))
                                                  , (λ v → \ j →
                                                      (glue {φ = φ} r[ fst ((snd (snd (snd (w itIsOne)) b)) v ∙ j) ]
                                                        (primComp (λ _ → A) _ (\ k → [ φ   ↦ r[ (snd (snd (snd (snd (w itIsOne)) b) v ∙ j) ∙ k ) ] , _ ↦
                                                                                     [ ~ j ↦ r[ fill (λ _ → A) φ (\ j →
                                                                                                     r[ snd (fst (snd (snd (w itIsOne)) b)) ∙ j ]) b k ]
                                                                                     , j   ↦ r[ _∙_ {y = unglue {φ = φ} (fst v)} (snd v) k ] ] ])
                                                                              b))
                                                      , ( (\ z -> fill (\ _ → A) _ (\ k →
                                                                       [ φ   ↦ r[ (snd (snd (snd (snd (w itIsOne)) b) v ∙ j) ∙ k ) ] , _ ↦
                                                                       [ ~ j ↦ r[ fill (λ _ → A) φ (\ j →
                                                                                       r[ snd (fst (snd (snd (w itIsOne)) b)) ∙ j ]) b k ]
                                                                       , j   ↦ r[ _∙_ {x = b} {y = unglue {φ = φ} (fst v)} (snd v)  k ] ] ])
                                                                       b
                                                                       z) )))
   where w : PartialP φ \ _ → Σ _ \ T → Equiv T A
         w = \ o → (T o , f o)


Equiv-contr : ∀ {a} (A : Set a) → Contr.isContr (Σ _ \ T → Equiv T A)
Equiv-contr A = (A , idEquiv) , (λ w →  \ i → let φ = (~ i ∨ i)
                                                  Tf : Partial (Σ _ \ T → Equiv T A) (~ i ∨ i)
                                                  Tf = [ ~ i ↦ r[ A , idEquiv ] , i ↦ r[ w ] ]
                                              in Glue A φ (\ o → fst (Tf o)) (\ o → snd (Tf o))
                                                 , unglue-equiv A φ (\ o → fst (Tf o)) (\ o → snd (Tf o)))

univ : ∀ {l} {A B : Set l} → Equiv A B → Path A B
univ = Univ.univ Equiv-contr


eqToPath : ∀ {l} {A B : Set l} → Equiv A B → Path A B
eqToPath {l} {A} {B} f = \ i → Glue B (~ i ∨ i) ([ ~ i ↦ (\ _ → A) , i ↦ (\ _ → B) ]) ([ ~ i ↦ r[ f ] , i ↦ r[ pathToEquiv (\ _ → B) ] ])

eqToPath' : ∀ {l} {A B : Set l} → Equiv A B → Path A B
eqToPath' {l} {A} {B} f = \ i → Glue B (~ i ∨ i) ([ ~ i ↦ (\ _ → A) , i ↦ (\ _ → B) ]) ([ ~ i ↦ r[ f ] , i ↦ r[ idEquiv ] ])


primitive
  primFaceForall : _

module FR (φ : I -> I) where
   δ = primFaceForall φ
   postulate
       ∀e : IsOne δ → ∀ i → IsOne (φ i)

module GlueIso {a b} {A : Set a} {φ : I} {T : Partial (Set b) φ} {f : (PartialP φ \ o → Equiv (T o) A)} where
  going : PartialP φ (\ o → Glue A φ T f → T o)
  going = r[ (\ x → x) ]
  back : PartialP φ (\ o → T o → Glue A φ T f)
  back = r[ (\ x → x) ]

  lemma : ∀ (b : PartialP φ (\ _ → Glue A φ T f)) → PartialP φ \ o → Path (unglue {φ = φ} (b o)) (fst (f o) (going o (b o)))
  lemma b = r[ refl ]

module CompGlue {la lb : I → _} (A : (i : I) → Set (la i)) (φ : I -> I) (T : ∀ i → Partial (Set (lb i)) (φ i))
                         (f : ∀ i → PartialP (φ i) \ o → Equiv (T i o) (A i)) where
   B : (i : I) -> Set (lb i)
   B = \ i → Glue (A i) (φ i) (T i) (f i)
   module Local (ψ : I) (b : ∀ i → Partial (B i) ψ) (b0 : B i0 {- [ ψ ↦ b i0 ] -}) where
     a : ∀ i → Partial (A i) ψ
     a i = \ o → unglue {φ = φ i} (b i o)
     module Forall (δ : I) (∀e : IsOne δ → ∀ i → IsOne (φ i)) where
       a0 : A i0
       a0 = unglue {φ = φ i0} b0
       a₁' = unsafeComp A ψ a a0
       t₁' : PartialP δ (\ o → T i1 (∀e o i1))
       t₁' = \ o → unsafeComp (λ i → T i (∀e o i)) ψ (\ i o' → GlueIso.going {φ = φ i} (∀e o i) (b i o')) (GlueIso.going {φ = φ i0} (∀e o i0) b0)
       w : PartialP δ _
       w = \ o → Pres.pres (\ i → fst (f i (∀e o i))) ψ (λ i x → GlueIso.going {φ = φ i} (∀e o i) (b i x)) (GlueIso.going {φ = φ i0} (∀e o i0) b0)
       a₁'' = unsafeComp (\ _ → A i1) (δ ∨ ψ) (\ j → unsafePOr δ ψ (\ o → w o ∙ j) (a i1)) a₁'
       g : PartialP (φ i1) _
       g o = (equiv (T i1 _) (A i1) (f i1 o) (δ ∨ ψ) (unsafePOr δ ψ t₁' (\ o' → GlueIso.going {φ = φ i1} o (b i1 o'))) a₁''
                        (unsafePOr δ ψ r[ refl ]  r[ GlueIso.lemma {φ = φ i1} (\ _ → b i1 itIsOne) o ]))
       t₁ : PartialP (φ i1) _
       t₁ o = fst (g o)
       α : PartialP (φ i1) _
       α o = snd (g o)
       a₁ = unsafeComp (\ j → A i1) (φ i1 ∨ ψ) (\ j → unsafePOr (φ i1) ψ (\ o → α o ∙ j) (a i1)) a₁''
       b₁ : Glue _ (φ i1) (T i1) (f i1)
       b₁ = unsafeGlue {φ = φ i1} t₁ a₁
     b1 = Forall.b₁ (FR.δ φ) (FR.∀e φ)

compGlue : {la lb : I → _} (A : (i : I) → Set (la i)) (φ : I -> I) (T : ∀ i → Partial (Set (lb i)) (φ i))
                         (f : ∀ i → PartialP (φ i) \ o → (T i o) → (A i)) →
                         (pf : ∀ i → PartialP (φ i) (λ o → isEquiv (T i o) (A i) (f i o))) →
           let
              B : (i : I) -> Set (lb i)
              B = \ i → primGlue (A i) (φ i) (T i) (f i) (pf i)
           in  (ψ : I) (b : ∀ i → Partial (B i) ψ) (b0 : B i0) → B i1
compGlue A φ T f pf ψ b b0 = CompGlue.Local.b1 A φ T (λ i p → (f i p) , (pf i p)) ψ b b0


{-# BUILTIN COMPGLUE compGlue #-}

not : Bool → Bool
not true = false
not false = true

notnot : ∀ y → y ≡ not (not y)
notnot true = refl
notnot false = refl

Σ-path : ∀ {a b} {A : Set a} {B : A → Set b} → {x y : A} → (p : Path x y) → {bx : B x} {by : B y} → PathP (\ i → B (p ∙ i)) bx by
           → Path {A = Σ A B} (x , bx) (y , by)
Σ-path pa pb = \ i → (pa ∙ i) , primPathPApply pb i

nothelp : ∀ y (y₁ : Σ Bool (λ x → Path y (not x))) →
          Path (not y , notnot y) y₁
nothelp y (true , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (true , sym eq')) refl (sym eq)
nothelp y (false , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (false , sym eq')) refl (sym eq)

notEquiv : Equiv Bool Bool
notEquiv = not , (\ { y → (not y , notnot y) , nothelp y })

test : Bool
test = primComp (\ i → univ {A = Bool} {B = Bool} notEquiv ∙ i)
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
test2 = primComp (\ i → eqToPath {A = Bool} {B = Bool} notEquiv ∙ i)
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
test3 = primComp (\ i → eqToPath' {A = Bool} {B = Bool} notEquiv ∙ i)
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

test05-test : ∀ j → primComp (\ i → D2 Bool) ( (j ∨ ~ j) ) (\ i → [ j ↦ r[ c1 ] , ~ j ↦ r[ c1 ] ]) c1 ≡ c1
test05-test j = refl

test5-test : ∀ j → primComp (\ i → D2 Bool) (j ∨ ~ j) (\ i → [ j ↦ r[ c1 ] , ~ j ↦ r[ c1 ] ]) c1 ≡ c1
test5-test j = refl

test6-test : ∀ (j : I -> I) → primComp (\ i → D2 Bool) (j i0) (\ i → \ o → c1) c1 ≡ c1
test6-test j = refl

test4-test : ∀ j → primComp (\ i → Bool) (j ∨ ~ j) (\ i → [ j ↦ r[ false ] , ~ j ↦ r[ false ] ] ) false ≡ false
test4-test j = refl


data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 20 _∷_

ListNot : List Bool ≡ List Bool
ListNot = \ i → List (univ {A = Bool} {B = Bool} notEquiv ∙ i)

trues : List Bool
trues = true ∷ true ∷ []

falses : List Bool
falses = primComp (\ i → ListNot ∙ i) i0 (\ _ → empty) trues

trues2 : List Bool
trues2 = primComp (\ i → trans ListNot ListNot ∙ i) i0 (\ _ → empty) trues

trues3 : List Bool
trues3 = primComp (\ i → let p = trans ListNot ListNot in
                         trans p p i)
                  i0
                  (\ _ → empty)
                  trues
