{-# OPTIONS --cubical --rewriting #-}

-- Ported from cubicaltt

module Cubical.Sigma where
open import Cubical.PathPrelude
open import Cubical.GradLemma
open import Cubical.Sub
open import Cubical.FromStdLib

and : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ) → Set ℓ
and A B = Σ A (λ _ → B)

lemPathSig : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (t u : Σ {ℓ} {ℓ'} A B) →
  Path (Path t u) (Σ (Path (fst t) (fst u))
  (λ p → PathP (λ i → B (p i)) (snd t) (snd u)))
lemPathSig {ℓ} {ℓ'} {A} {B} t u = isoToPath f g s r where
   T0 = Path {A = Σ {ℓ} {ℓ'} A B} t u
   T1  = Σ (Path {A = A} (fst t) (fst u))
           (λ p → PathP (λ i → B (p i)) (snd t) (snd u))
   f : T0 → T1
   f q = (λ i → fst (q i)) , (λ i → snd (q i))
   g : T1 → T0
   g z = λ i → ((fst z) i , (snd z) i)
   s : (z : T1) → Path {A = T1} (f (g z)) z
   s z = refl
   r : (q : T0) →  Path {A = T0} (g (f q)) q
   r q = refl

nonDepPath : ∀{ℓ} {A : Set ℓ} → (t u : A) → (t ≡ u) ≡ (PathP (λ i → A) t u)
nonDepPath {ℓ} {A} t u = isoToPath g f r s where
  T0 : Set ℓ
  T0 = Path t u

  T1 : Set ℓ
  T1 = PathP (λ i → A) t u

  f : T1 → T0
  f p i = p i

  g : T0 → T1
  g q i = q i

  s : (z : T0) → Path (f (g z)) z
  s z = refl
  r : (q : T1) →  Path (g (f q)) q
  r q = refl

congP : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) →
   Path x y → Path (f x) (f y)
congP f p = λ i → f (p i)

lemPathAnd : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} (t u : and {ℓ} A B) →
   Path (Path  t u)
   (and (Path (t .fst) (u .fst))
       (Path (t .snd) (u .snd)))
lemPathAnd {ℓ} {A} {B} t u  =
 let p = lemPathSig t u in
 let q : Path (Σ {ℓ} (Path (fst t) (fst u))
           (λ p₁ → PathP (λ i → B) (snd t) (snd u)))
           (and (Path (t .fst) (u .fst)) (Path (t .snd) (u .snd)))
     q = congP (and _) ((sym (nonDepPath _ _)))
 in
 trans p q

lemTransp : {A : Set} (a : A) → Path a (transp (λ _ →  A) a)
lemTransp {A} a i =  safeFill (λ _ → A) i0 (λ _ → empty) (inc a) i


funDepTr : ∀{ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (a0 a1 : A)
  (p : Path {A = A} a0 a1) (u0 : P a0) (u1 : P a1) →
  Path {A = Set ℓ'} (PathP (λ i → P (p i)) u0 u1)
  (Path {A = P a1} (transp (λ i → P (p i)) u0) u1)
funDepTr {ℓ} {ℓ'} {A} {P} a0 a1 p u0 u1 = trans q r where
  q :  Path {A = Set ℓ'} (PathP (λ i → P (p i)) u0 u1)
              (PathP (λ _ → P a1) (transp (λ i → P (p i)) u0) u1)
  q = λ j → PathP (λ i → P (p (j ∨ i)))
      (ouc (safeComp (λ i → P (p (j ∧ i))) (~ j)
      (λ i → (λ { (j = i0) → u0 })) (inc u0))) u1

  r :  Path {A = Set ℓ'} (PathP (λ _ → P a1) (transp (λ i → P (p i)) u0) u1)
              (Path {A = P a1} (transp (λ i → P (p i)) u0) u1)
  r = sym (nonDepPath ((transp (λ i → P (p i)) u0)) u1)


module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where
  lem2 : (t u : Σ {ℓ} {ℓ'} A B) (p : Path (fst t) (fst u)) →
    (PathP (λ i → B (p i)) (snd t) (snd u)) ≡
    (transp (λ i → B (p i)) (snd t) ≡ snd u)
  lem2 t u p = funDepTr (fst t) (fst u) p (snd t) (snd u)

  corSigProp : {pB : (x : A) →
    isProp (B x)} (t u : Σ A B) (p : Path (fst t) (fst u)) →
    isProp (PathP (λ i → B (p i)) (snd t) (snd u))
  corSigProp {pB} t u p = substInv {A = Set ℓ'}{P = isProp} rem rem1 where
    P : I → Set ℓ'
    P = λ i → B (p i)

    T0 : Set ℓ'
    T0 = PathP P (snd t) (snd u)

    T1 : Set ℓ'
    T1 = Path (transp P (snd t)) (snd u)

    rem : Path T0 T1
    rem = lem2 t u p

    v2 : B (fst u)
    v2 = transp P (snd t)

    rem1 : isProp T1
    rem1 = propSet (pB (fst u)) v2 (snd u)


  corSigSet : {sB : (x : A)
    → isSet (B x)} (t u : Σ A B) (p : Path (fst t) (fst u))
    → isProp (PathP (λ i → B (p i)) (snd t) (snd u))
  corSigSet {sB} t u p = substInv {A = Set ℓ'} {isProp} rem rem1 where
    P : I → Set ℓ' -- Path (B (fst t)) (B (fst u))
    P = λ i → B (p i)

    T0 : Set ℓ'
    T0 = PathP P (snd t) (snd u)

    T1 : Set ℓ'
    T1 = Path (transp P (snd t)) (snd u)

    rem : Path T0 T1
    rem = lem2 t u p
    -- funDepTr (B t .fst) (B u .fst) P t .snd u .snd

    v2 : B (u .fst)
    v2 = transp P (t .snd)

    rem1 : isProp T1
    rem1 = sB (u .fst) v2 (u .snd)

  setSig : {sA : isSet A}{sB : (x : A)→ isSet (B x)}(t u : Σ A B)→ isProp(t ≡ u)
  setSig {sA} {sB} t u = substInv {A = Set (ℓ-max ℓ ℓ')} {isProp}
      rem3 rem2 where
    T : Set ℓ
    T = Path (t .fst) (u .fst)
    C : T →  Set ℓ'
    C p =  PathP (λ i → B (p i)) (t .snd) (u .snd)
    rem : (p : T) →  isProp (C p)
    rem p = corSigSet {sB = sB} t u p
    rem1 : isProp T
    rem1 = sA (t .fst) (u .fst)
    rem2 : isProp (Σ T (λ p → C p))
    rem2 =  propSig {A = T} {B = C} rem1 rem
    rem3 : Path (Path t u) (Σ T  (λ p → C p))
    rem3 = lemPathSig t u

groupoid : ∀ {ℓ} (A : Set ℓ) → Set ℓ
groupoid A = (a b : A) → isSet (Path a b)

corSigGroupoid : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (gB : (x : A)
   → groupoid (B x)) (t u : Σ A B) (p : Path (t .fst) (u .fst))
   → isSet (PathP (λ i → B (p i)) (t .snd) (u .snd))
corSigGroupoid {ℓ} {ℓ'} {A} {B} gB t u p =
   substInv {A = Set ℓ'} {isSet} rem rem1
-- = substInv U set T0 T1 rem rem1
 where P : I → Set ℓ' -- Path (B (t .fst)) (B (u .fst))
       P = λ i → B (p i)
       T0 : Set ℓ'
       T0 = PathP P (t .snd) (u. snd)
       T1 : Set ℓ'
       T1 = Path ((transp P (t .snd))) ((u .snd))
       rem : Path T0 T1
       rem = lem2 t u p -- funDepTr (B t .fst) (B u .fst) P t .snd u .snd
       v2 : B (u .fst)
       v2 = transp P (t .snd)
       rem1 : isSet T1
       rem1 = gB (u .fst) v2 (u .snd)

groupoidSig : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (gA : groupoid A)
  (gB : (x : A) → groupoid (B x)) (t u : Σ A B)→ isSet (Path t u)
groupoidSig {ℓ} {ℓ'} {A} {B} gA gB t u = substInv {A = Set (ℓ-max ℓ ℓ')}
    {isSet} rem3 rem2 where
  T : Set ℓ
  T = Path (t .fst) (u .fst)
  C  : T →  Set ℓ'
  C p = PathP (λ i →  B (p i)) (t .snd) (u .snd)
  rem : (p : T) → isSet (C p)
  rem p = corSigGroupoid gB t u p
  rem1 : isSet T
  rem1 = gA (t .fst) (u .fst)
  rem2 : isSet (Σ T (λ p → C p) )
  rem2 =  setSig {sA = rem1} {sB = rem}
  rem3 : Path (Path t u) (Σ T (λ p → C p))
  rem3 = lemPathSig t u

lemContr' : ∀ {ℓ} {A : Set ℓ} (pA : isProp A) (a : A) → isContr A
lemContr' {ℓ} {A} pA a = (a , rem)
  where rem : (y : A) → Path a y
        rem y = pA a y

lem3  : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (pB : (x : A) → isProp (B x))
  (t u : Σ A B) (p : Path (t .fst) (u .fst)) →
  isContr (PathP (λ i → B (p i)) (t .snd) (u .snd))
lem3 {ℓ} {ℓ'} {A} {B} pB t u p =
    lemContr' (substInv {A = Set ℓ'} {isProp} rem rem1) rem2 where
  P : I → Set ℓ' -- Path (B (t .fst)) (B (u .fst))
  P = λ i → B (p i)
  T0 : Set ℓ'
  T0 = PathP P (t .snd) (u .snd)
  T1 : Set ℓ'
  T1 = Path (transp P (t .snd)) (u .snd)
  rem : Path T0 T1
  rem = lem2 t u p
  v2 : B (u .fst)
  v2 = transp P (t .snd)
  rem1 : isProp T1
  rem1 = propSet (pB (u .fst)) v2 (u .snd)
  rem2 : T0
  rem2 = transp (λ i → rem (~ i)) (pB (u .fst) v2 (u .snd))

lem6 : ∀ {ℓ} (A : Set ℓ) (P : A → Set ℓ) (cA : (x : A) → isContr (P x)) →
  Path {A = Set ℓ} (Σ A ( λ x → P x)) A
lem6 {ℓ} A P cA = isoToPath f g t s where
  T : Set ℓ
  T = Σ A (λ x → P x)
  f : T → A
  f z  = z .fst
  g : A →  T
  g x = (x , ((cA x) .fst))
  s : (z : T) → Path (g (f z)) z
  s z = λ i → ((z .fst) , (((cA (z .fst)) .snd) (z .snd))  i)
  t : (x : A) →  Path (f (g x)) x
  t x = refl

lemSigProp : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {pB : (x : A) →
  isProp (B x)} (t u : Σ A B) → Path (Path t u) (Path (t .fst) (u .fst))
lemSigProp {ℓ} {A} {B} {pB} t u = trans rem2 rem1
  where
   T : Set ℓ
   T = Path (t .fst) (u .fst)
   C : T → Set ℓ
   C p = PathP (λ i → B (p i)) (t .snd) (u .snd)
   rem : (p : T) → isContr (C p)
   rem p = lem3 pB t u p
   rem1 : Path (Σ T (λ p → C p)) T
   rem1 = lem6 T C rem
   rem2 : Path (Path t u) (Σ T (λ p → C p))
   rem2 = lemPathSig t u

setGroupoid : ∀{ℓ}{A : Set ℓ}(sA : isSet {ℓ} A) (a0 a1 : A) → isSet (Path a0 a1)
setGroupoid {ℓ} sA a0 a1 = propSet (sA a0 a1)

propGroupoid : ∀ {ℓ} {A : Set ℓ} (pA : isProp A) → groupoid A
propGroupoid pA = setGroupoid (propSet pA)
