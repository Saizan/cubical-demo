{-# OPTIONS --cubical #-}

-- Ported from cubicaltt

module Cubical.Sigma where
open import Cubical.PathPrelude
open import Cubical.GradLemma
open import Cubical.Sub
open import Cubical.FromStdLib
open import Cubical.NType
open import Cubical.NType.Properties

and : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ) → Set ℓ
and A B = Σ A (λ _ → B)

-- 2.7.2 in HoTT
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
nonDepPath {ℓ} {A} t u = refl

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

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : A → Set ℓb} where
  -- Theorem 7.1.8 in HoTT:

  -- Σ preserves contractibility in the following sense:
  sigPresContr : isContr A → (∀ a → isContr (B a)) → isContr (Σ A B)
  sigPresContr (a0 , contrA) a→contrB =
    let
      (b0 , contrB) = a→contrB a0
      P : (y : A) → a0 ≡ y → Set ℓb
      P y eq = ∀ b' → (λ i → B (eq i)) [ b0 ≡ b' ]
    in (a0 , b0) , λ {(a , b) →
      let
        eqA : a0 ≡ a
        eqA = contrA a
        eqB : (Ba' : B a) → (λ j → B (eqA j)) [ b0 ≡ Ba' ]
        eqB = pathJ P contrB a eqA
        u : (λ i → B (eqA i)) [ b0 ≡ b ]
        u = eqB b
      in λ i → eqA i , u i}

  sigPresProp : isProp A → (∀ a → isProp (B a)) → isProp (Σ A B)
  sigPresProp = propSig

sigPresNType : {ℓa ℓb : Level} {A : Set ℓa} {B : A → Set ℓb} {n : TLevel}
  → HasLevel n A → (∀ a → HasLevel n (B a)) → HasLevel n (Σ A B)
sigPresNType {n = ⟨-2⟩} = sigPresContr
sigPresNType {n = S ⟨-2⟩} = sigPresProp
sigPresNType {ℓb = ℓb} {A = A} {B} {S (S n)} ntA a→ntB (a₁ , b₁) (a₂ , b₂) =
  let
    T = a₁ ≡ a₂
    U p = (λ i → B (p i)) [ b₁ ≡ b₂ ]
    V = Σ T U
    t : HasLevel (S n) T
    t = ntA a₁ a₂
    u : (eqa : T) → HasLevel (S n) (U eqa)
    u eqa =
      let
        f : (b : B a₁) → HasLevel (S n) ((λ i → B a₁) [ b₁ ≡ b ])
        f = a→ntB a₁ b₁
        P : (y : A) → a₁ ≡ y → Set ℓb
        P y eq = ∀ b → HasLevel (S n) ((λ i → B (eq i)) [ b₁ ≡ b ])
      in pathJ P f a₂ eqa b₂
    -- Inductive hypothesis.
    prev : HasLevel (S n) V
    prev = sigPresNType {n = S n} t u
    equivl : V ≃ ((a₁ , b₁) ≡ (a₂ , b₂))
    equivl = pathToEquiv (sym (lemPathSig (a₁ , b₁) (a₂ , b₂)))
  in equivPreservesNType {n = S n} equivl prev
