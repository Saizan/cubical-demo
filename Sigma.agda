{-# OPTIONS --cubical --rewriting #-}

-- Ported from cubicaltt

module Sigma where
open import PathPrelude
open import GradLemma
open import Sub
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

-- record Σ {l m : Level} (A : Set l) (B : A → Set m) : Set (l ⊔ m) where
--   constructor _,_
--   field
--     fst : A
--     snd : B fst

-- open Σ

and : ∀ {l} (A : Set l) (B : Set l) → Set  l
and A B = Σ A (\ _ → B)

lemPathSig : ∀ {l m} {A : Set l} {B : A -> Set m} (t u : Σ {l} {m} A B) →
                     Path (Path t u) 
                     (Σ (Path (fst t) (fst u))
                     (\ p -> PathP (λ i → B (p i)) (snd t) (snd u))) 
lemPathSig {l} {m} {A} {B} t u = isoToPath f g s r where
   T0 = Path {A = Σ {l} {m} A B} t u
   T1  = Σ (Path {A = A} (fst t) (fst u)) (\ p -> PathP (\ i -> B (p i)) (snd t) (snd u)) 
   f : T0 -> T1 
   f q = (\ i → fst (q i)) , (\ i → snd (q i))
   g : T1 → T0 
   g z = \ i → ((fst z) i , (snd z) i)
   s : (z : T1) → Path {A = T1} (f (g z)) z 
   s z = refl 
   r : (q : T0) →  Path {A = T0} (g (f q)) q 
   r q = refl

nonDepPath : ∀{l}  {A : Set l} → (t u : A) → Path (Path t u) (PathP (\ i → A) t u)
nonDepPath {l} {A} t u = isoToPath g f r s
  where 
  
    T0 : Set l
    T0 = Path t  u
  
    T1 : Set l
    T1 = PathP (\ i → A) t u

    f : T1 → T0
    f p i = p i

    g : T0 → T1
    g q i = q i

    s : (z : T0) → Path (f (g z)) z 
    s z = refl 
    r : (q : T1) →  Path (g (f q)) q 
    r q = refl



congP : ∀ {u} {v} → {A : Set u} {B : Set v} → {x y : A} → (f : A → B) → Path x y →  Path (f x) (f y)
congP f p = \ i → f (p i)


lemPathAnd : ∀ {l} {A : Set l} {B : Set l} (t u : and {l} A B) →
   Path (Path  t u) 
   (and (Path (t .fst) (u .fst)) 
       (Path (t .snd) (u .snd))) 
lemPathAnd {l} {A} {B} t u  = 
 let p = lemPathSig t u in
 let q : Path (Σ {l} (Path (fst t) (fst u))
           (λ p₁ → PathP (λ i → B) (snd t) (snd u)))
           (and (Path (t .fst) (u .fst)) (Path (t .snd) (u .snd)))
     q = congP (and _) ((sym (nonDepPath _ _)))
 in
 trans p q

-- from PathPrelude where clause
transport : ∀ {l : I → _} (E : (i : I) → Set (l i)) → E i0 → E i1
transport E x = primComp E i0 (\ _ → empty) x

lemTransp : {A : Set} (a : A) → Path a (transport (\_ →  A) a) 
lemTransp {A} a i =  safeFill (\_ → A) i0 (\_ → empty) (inc a) i


funDepTr : ∀{l m} {A : Set l} {P : A → Set m} (a0 a1 : A) (p : Path {A = A} a0 a1) (u0 : P a0) (u1 : P a1) → 
  Path {A = Set m} (PathP (\ i → P (p i)) u0 u1) 
                 (Path {A = P a1} (transport (\ i → P (p i)) u0) u1)
funDepTr {l} {m} {A} {P} a0 a1 p u0 u1 = trans q r
   where
     q :  Path {A = Set m} (PathP (\ i → P (p i)) u0 u1) 
                 (PathP (\_ → P a1) (transport (\ i → P (p i)) u0) u1)
     q = \j → PathP (\ i → P (p (j ∨ i))) 
         (ouc (comp (\ i → P (p (j ∧ i))) (~ j) 
         (\ i → (\ { (j = i0) → u0 })) (inc u0))) u1
     
     r :  Path {A = Set m} (PathP (\_ → P a1) (transport (\ i → P (p i)) u0) u1)
                 (Path {A = P a1} (transport (\ i → P (p i)) u0) u1)
     r = sym (nonDepPath ((transport (\ i → P (p i)) u0)) u1)


subst : ∀ {l m} {A : Set l} {P : A → Set m} (a b : A) (p : Path a b) → P a → P b
subst {l} {m} {A} {P} a b p p0 = pathJ {l} {m} (\ (y : A) → \_ → P y) p0 b p

substInv : ∀ {l m} {A : Set l} {P : A → Set m} (a x : A) (p : Path a x) → P x → P a 
substInv {l} {m} a x p  =  subst {l} {m} x a (\ i → p (~ i)) 


lem2 : ∀ {l m} {A : Set l} {B : A → Set m} (t u : Σ {l} {m} A B) (p : Path (fst t) (fst u)) → Path (PathP (\ i →  B (p i)) (snd t) (snd u)) (Path (transport (\ i → B (p i)) (snd t)) (snd u))
lem2 {l} {m} {A} {B} t u p = funDepTr (fst t) (fst u) p (snd t) (snd u) 

corSigProp : ∀ {l m} {A : Set l} {B : A → Set m} {pB : (x : A) → prop (B x)} (t u : Σ A B) (p : Path (fst t) (fst u)) → prop (PathP (\i → B (p i)) (snd t) (snd u))
corSigProp {l} {m} {A} {B} {pB} t u p = substInv {A = Set m} {P = prop} T0 T1 rem rem1
  where 
    P : I → Set m
    P = \i → B (p i)
  
    T0 : Set m
    T0 = PathP P (snd t) (snd u)

    T1 : Set m
    T1 = Path (transport P (snd t)) (snd u)
  
    rem : Path T0 T1
    rem = lem2 t u p

    v2 : B (fst u)
    v2 = transport P (snd t)

    rem1 : prop T1
    rem1 = propSet (pB (fst u)) v2 (snd u)


corSigSet : ∀ {l m} {A : Set l} {B : A → Set m} {sB : (x : A) → set (B x)} (t u : Σ A B) (p : Path (fst t) (fst u))
  →  prop (PathP (\ i → B (p i)) (snd t) (snd u)) 
corSigSet {l} {m} {A} {B} {sB} t u p = substInv {A = Set m} {prop} T0 T1 rem rem1
  where 
    P : I → Set m -- Path (B (fst t)) (B (fst u))
    P = \ i → B (p i)

    T0 : Set m
    T0 = PathP P (snd t) (snd u)

    T1 : Set m
    T1 = Path (transport P (snd t)) (snd u)
    
    rem : Path T0 T1 
    rem = lem2 t u p 
    -- funDepTr (B t .fst) (B u .fst) P t .snd u .snd
    
    v2 : B (u .fst)
    v2 = transport P (t .snd)

    rem1 : prop T1 
    rem1 = sB (u .fst) v2 (u .snd)

setSig : ∀ {l m} {A : Set l} {B : A → Set m} {sA : set A} {sB : (x : A) → set (B x)}
  (t u : Σ A B) →  prop (Path t u) 
setSig {l} {m} {A} {B} {sA} {sB} t u = substInv {A = Set (m ⊔ l)} {prop} (Path t u) (Σ T (\ p →  C p)) rem3 rem2
  where
    T : Set l
    T = Path (t .fst) (u .fst)
    C : T →  Set m
    C p =  PathP (\ i → B (p i)) (t .snd) (u .snd)
    rem : (p : T) →  prop (C p) 
    rem p = corSigSet {A = A} {B = B} {sB = sB} t u p
    rem1 : prop T 
    rem1 = sA (t .fst) (u .fst)
    rem2 : prop (Σ T (\ p → C p))
    rem2 =  propSig {A = T} {B = C} rem1 rem
    rem3 : Path (Path t u) (Σ T  (\ p → C p))
    rem3 = lemPathSig t u

groupoid : ∀ {l} (A : Set l) → Set l 
groupoid A = (a b : A) → set (Path a b)

corSigGroupoid : ∀ {l m} {A : Set l} {B : A → Set m} (gB : (x : A) → groupoid (B x)) (t u : Σ A B) (p : Path (t .fst) (u .fst))
   →  set (PathP (\ i → B (p i)) (t .snd) (u .snd)) 
corSigGroupoid {l} {m} {A} {B} gB t u p = substInv {A = Set m} {set} T0 T1 rem rem1
-- = substInv U set T0 T1 rem rem1
 where P : I → Set m -- Path (B (t .fst)) (B (u .fst)) 
       P = \i → B (p i)
       T0 : Set m
       T0 = PathP P (t .snd) (u. snd)
       T1 : Set m
       T1 = Path ((transport P (t .snd))) ((u .snd))
       rem : Path T0 T1 
       rem = lem2 t u p -- funDepTr (B t .fst) (B u .fst) P t .snd u .snd
       v2 : B (u .fst) 
       v2 = transport P (t .snd)
       rem1 : set T1 
       rem1 = gB (u .fst) v2 (u .snd)

groupoidSig : ∀ {l m} {A : Set l} {B : A → Set m} (gA : groupoid A) (gB : (x : A) → groupoid (B x)) (t u : Σ A B)→ set (Path t u) 
groupoidSig {l} {m} {A} {B} gA gB t u = substInv {A = Set (m ⊔ l)} {set} (Path t u) (Σ T (\ p → C p)) rem3 rem2
  where
    T : Set l
    T = Path (t .fst) (u .fst)
    C  : T →  Set m
    C p = PathP (\ i →  B (p i)) (t .snd) (u .snd)
    rem : (p : T) → set (C p) 
    rem p = corSigGroupoid gB t u p
    rem1 : set T 
    rem1 = gA (t .fst) (u .fst)
    rem2 : set (Σ T (\ p → C p) )
    rem2 =  setSig {sA = rem1} {sB = rem}
    rem3 : Path (Path t u) (Σ T (\ p → C p))
    rem3 = lemPathSig t u

lemContr : ∀ {l} {A : Set l} (pA : prop A) (a : A) → Contr.isContr A 
lemContr {l} {A} pA a = (a , rem)
  where rem : (y : A) → Path a y 
        rem y = pA a y

lem3  : ∀ {l m} {A : Set l} {B : A → Set m} (pB : (x : A) → prop (B x)) (t u : Σ A B) (p : Path (t .fst) (u .fst)) →  Contr.isContr (PathP (\ i → B (p i)) (t .snd) (u .snd)) 
lem3 {l} {m} {A} {B} pB t u p = lemContr (substInv {A = Set m} {prop} T0 T1 rem rem1) rem2
   where 
     P : I → Set m -- Path (B (t .fst)) (B (u .fst)) 
     P = \ i → B (p i)
     T0 : Set m
     T0 = PathP P (t .snd) (u .snd)
     T1 : Set m
     T1 = Path (transport P (t .snd)) (u .snd)
     rem : Path T0 T1 
     rem = lem2 t u p
     v2 : B (u .fst) 
     v2 = transport P (t .snd)
     rem1 : prop T1 
     rem1 = propSet (pB (u .fst)) v2 (u .snd) 
     rem2 : T0 
     rem2 = transport (\ i → rem (~ i)) (pB (u .fst) v2 (u .snd))

lem6 : ∀ {l} (A : Set l) (P : A → Set l) (cA : (x : A) → Contr.isContr (P x)) → Path {A = Set l} (Σ A ( \ x → P x)) A 
lem6 {l} A P cA = isoToPath f g t s
   where
     T : Set l
     T = Σ A (\ x → P x)
     f : T → A 
     f z  = z .fst
     g : A →  T 
     g x = (x , ((cA x) .fst))
     s : (z : T) → Path (g (f z)) z 
     s z = \ i → ((z .fst) , (((cA (z .fst)) .snd) (z .snd))  i)
     t : (x : A) →  Path (f (g x)) x 
     t x = refl 

lemSigProp : ∀ {l} {A : Set l} {B : A → Set l} {pB : (x : A) → prop (B x)} (t u : Σ A B) → Path (Path t u) (Path (t .fst) (u .fst)) 
lemSigProp {l} {A} {B} {pB} t u = {!!}
--  compPath U (Path (Σ A B) t u) ((p:Path A (t .fst) (u .fst)) * PathP (<i> B (p@i)) (t .snd) (u .snd)) (Path A (t .fst) (u .fst)) rem2 rem1
  where
   T : Set l
   T = Path (t .fst) (u .fst)
   C : T → Set l
   C p = PathP (\i → B (p i)) (t .snd) (u .snd)
   rem : (p : T) → Contr.isContr (C p) 
   rem p = lem3 pB t u p
   rem1 : Path (Σ T (\ p → C p)) T 
   rem1 = lem6 T C rem
   rem2 : Path (Path t u) (Σ T (\p → C p))
   rem2 = lemPathSig t u 

setGroupoid : ∀ {l} {A : Set l} (sA : set {l} A) (a0 a1 : A) → set (Path a0 a1) 
setGroupoid {l} sA a0 a1 = propSet (sA a0 a1)

propGroupoid : ∀ {l} {A : Set l} (pA : prop A) → groupoid A 
propGroupoid pA = setGroupoid (propSet pA)
