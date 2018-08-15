{-# OPTIONS --cubical --caching #-}
module Cubical.Examples.Brunerie where

open import Cubical.PathPrelude hiding (subst; J)
open import Cubical.Examples.Circle
open import Cubical.FromStdLib
open import Cubical.Examples.Int
open import Cubical.Examples.Torus
open import Cubical.NType.Properties


refl2 : ∀ {l} {A : Set l} {x : A} → Square (refl {x = x}) refl refl refl
refl2 {x = x} _ _ = x

constSquare : {A : Set} {a : A} (p : Path a a) → Square p p p p
constSquare {A} {a} p i j =
  primHComp A _
          (\ k → \ { (i = i0) -> p (j ∨ ~ k)
                  ; (i = i1) -> p (j ∧ k)
                  ; (j = i0) -> p (i ∨ ~ k)
                  ; (j = i1) -> p (i ∧ k)
                  })
           a

Cube : ∀ {l} {A : Set l} {a0 b0 c0 d0 a1 b1 c1 d1 : A}
         {ab0 cd0} {ac0 : Path a0 c0} {bd0 : Path b0 d0}
         {ab1 cd1} {ac1 : Path a1 c1} {bd1 : Path b1 d1}
         (s0 : Square ab0 cd0 ac0 bd0) (s1 : Square ab1 cd1 ac1 bd1)
         {pa pb pc pd}
         (sab : Square ab0 ab1 pa pb) (scd : Square cd0 cd1 pc pd)
         (sac : Square ac0 ac1 pa pc) (sbd : Square bd0 bd1 pb pd) → Set _
Cube s0 s1 sab scd sac sbd = PathP (\ i → Square (sab i) (scd i) (sac i) (sbd i)) s0 s1



S1 = S¹

pattern base1 = base
pattern loop1 i = loop i

loopS1 : Set
loopS1 = Path base1 base1

data joinS1 : Set where
  inl : (a : S1) → joinS1
  inr : (a : S1) → joinS1
  push : ∀ a b  → inl a ≡ inr b


data S2 : Set where
  base2 : S2
  loop2 : Square (refl {x = base2}) refl refl refl

data S3 : Set where
  base3 : S3
  loop3 : Cube (refl2 {x = base3}) refl2 refl2 refl2 refl2 refl2



ptType : Set _
ptType = Σ Set \ A → A

pt : (A : ptType) → A .fst
pt A = A .snd

boolpt : ptType
boolpt = (Bool , true)

S1pt : ptType
S1pt = (S1 , base1)
S2pt : ptType
S2pt = (S2 , base2)
S3pt : ptType
S3pt = (S3 , base3)

Omega : (A : ptType) → ptType
Omega A = (Path (pt A) (pt A) , refl)
Omega2 : (A : ptType) → ptType
Omega2 A = Omega (Omega A)
Omega3 : (A : ptType) → ptType
Omega3 A = Omega2 (Omega A)

mapOmegaRefl : (A : ptType) {B : Set} (h : A .fst -> B)
                  (p : Omega A .fst) → (Omega (B , h (pt A))) .fst
mapOmegaRefl A h p i = h (p i)

mapOmegaRefl2 : (A : ptType) {B : Set} (h : A .fst -> B)
                  (p : Omega2 A .fst) → (Omega2 (B , h (pt A))) .fst
mapOmegaRefl2 A h p i j = h (p i j)

mapOmegaRefl3 : (A : ptType) {B : Set} (h : A .fst -> B)
                  (p : Omega3 A .fst) → (Omega3 (B , h (pt A))) .fst
mapOmegaRefl3 A h p i j k = h (p i j k)


joinpt : ptType
joinpt = (joinS1 , inl base1)

-- The first type:
T1 : Set
T1 = PathP (\ i → PathP (\ j → Path (inl (loop i)) (inr (loop j)))
                        (\ j → push (loop i) base1 j)
                        (\ j → push (loop i) base1 j))
           (\ i j → push base1 (loop i) j)
           (\ i j → push base1 (loop i) j)

-- The second type without loop:
T2 : Set
T2 = PathP (\ i → PathP (\ j → Path (inl base1) (inr base1))
                        (\ j → push base1 base1 j)
                        (\ j → push base1 base1 j))
           (\ i j → push base1 base1 j)
           (\ i j → push base1 base1 j)



T12 : T1 ≡ T2
T12 k =
     PathP (\ i → PathP (\ j → Path (inl (loop (i ∧ ~ k))) (inr (loop (j ∧ ~ k))))
                        (\ j → push (loop (i ∧ ~ k)) base1 j)
                        (\ j → push (loop (i ∧ ~ k)) (loop (~ k)) j))
           (\ i j → push base1 (loop (i ∧ ~ k)) j)
           (\ i j → push (loop (~ k)) (loop (i ∧ ~ k)) j)

cubestep1 : T2
cubestep1 = primTransp (\ i → T12 i) i0 (\ i j k → push (loop i) (loop j) k)


goalcube : Cube (refl2 {x = inl base1}) refl2 refl2 refl2 refl2 refl2
goalcube i j k =
  primHComp joinS1 _
     (\ { l (k = i0) -> inl base1
        ; l (k = i1) -> push base1 base1 (~ l)
        ; l (j = i0) -> push base1 base1 (k ∧ ~ l)
        ; l (j = i1) -> push base1 base1 (k ∧ ~ l)
        ; l (i = i0) -> push base1 base1 (k ∧ ~ l)
        ; l (i = i1) -> push base1 base1 (k ∧ ~ l)
        })
      (cubestep1 i j k)


e : S3 -> joinS1
e base3 = inl base1
e (loop3 i j k) = goalcube i j k

merid : S1 -> Path base2 base2
merid base1 _ = base2
merid (loop i) = \ j → loop2 i j

alpha : joinS1 -> S2
alpha (inl x) = base2
alpha (inr y) = base2
alpha (push x y i) = mytrans (merid y) (merid x) i

subst : ∀ {l p} {A : Set l} (P : A -> Set p) {a b : A} (p : Path a b) (e : P a) → P b
subst P p e =
  primTransp (\ i → P (p i)) i0 e

J : ∀ {l p} {A : Set l} {a : A} (C : (x : A) -> Path a x -> Set p)
      (d : C a refl) (x : A) (p : Path a x) → C x p
J C d x p = subst (\ z → C (z .fst) (z .snd)) (contrSingl p) d

propIsEquivDirect = propIsEquiv -- not the most efficient

ua = equivToPath


rotLoop : (a : S1) -> Path a a
rotLoop base1 i = loop1 i
rotLoop (loop1 i) j = constSquare loop1 i j

rot : S1 -> S1 -> S1
rot base1 y = y
rot (loop1 i) y = rotLoop y i


pathSIntroS1 : ∀ {p} (C : S1 -> Set p) (c : C base1)
           (w : Path (subst C loop c) c) → PathP (\ i → C (loop i)) c c
pathSIntroS1 C c w =
  primTransp (\ j → PathP (\ i → C (loop (~ j ∨ i)))
                      (primTransp (\ i → C (loop (~ j ∧ i))) j c) c) i0 w

s1elim : ∀ {p} → (C : S1 -> Set p)
       (c : C base1) (p : Path (subst C loop1 c) c) →
  (x : S1) -> C x
s1elim C c p base1 = c
s1elim C c p (loop i) = pathSIntroS1 C c p i


rotIsEquiv : (a : S1) -> isEquiv S1 S1 (rot a)
rotIsEquiv = s1elim (λ z → isEquiv S1 S1 (rot z)) (idEquiv .snd)
             (propIsEquiv (rot (loop i1)) (subst (λ z → isEquiv S1 S1 (rot z)) loop1 (idEquiv .snd)) (idEquiv .snd))


rotpath : (x : S1) → S1 ≡ S1
rotpath x = ua (rot x , rotIsEquiv x)

HopfSquare : ∀ {l} → (A : Set l) → (ua (idEquiv {A = A})) ≡ refl
HopfSquare A j i =
  Glue A (~ i ∨ i ∨ j) (\ _ → A) (\ _ → idEquiv)

Hopf : S2 -> Set
Hopf base2 = S1
Hopf (loop2 i j) = primHComp (Set _) _
                       (\ k →
                       \ { (i = i0) -> HopfSquare S1 k j
                       ; (i = i1) -> HopfSquare S1 k j
                       ; (j = i0) -> S1
                       ; (j = i1) -> S1
                       })
                       (rotpath (loop i) j)


-----------------------------

-- tests

test0To2 : (Omega3 S3pt) .fst
test0To2 = loop3

f3 : (Omega3 S3pt) .fst -> (Omega3 joinpt) .fst
f3 = mapOmegaRefl3 S3pt e

test0To3 : Omega3 joinpt .fst
test0To3 = f3 test0To2

f4 : (Omega3 joinpt) .fst -> (Omega3 S2pt) .fst
f4 = mapOmegaRefl3 (joinpt) alpha

test0To4 : (Omega3 S2pt) .fst
test0To4 = f4 test0To3


-- This is the problematic stuff:
module M (x : (Omega3 S2pt) .fst) where
    innerpath : ∀ i j → Hopf (x i j i1)
    innerpath i j = primTransp (\ k → Hopf (x i j k)) i0 base1

    problem : Path (pos zero) (pos zero)
    problem i = primTransp (\ j → helix (innerpath i j)) i0 (pos zero)

    -- -- This term contains a ton of hcomp U:
    problempath : Path (helix (primTransp (\ k → Hopf (x k i0 k)) i0 base1))
                         (helix (primTransp (\ k → Hopf (x k i1 k)) i0 base1))
    problempath j = helix (primTransp (\ k → Hopf (x k j k)) i0 base1)

test = M.problem test0To4

-- innerpath : ∀ i j → Hopf (test0To4 i j i1)
-- innerpath i j = primTransp (\ k → Hopf (test0To4 i j k)) i0 base1

-- problem : Path (pos zero) (pos zero)
-- problem i = primTransp (\ j → helix (innerpath i j)) i0 (pos zero)

-- -- -- This term contains a ton of hcomp U:
-- problempath : Path (helix (primTransp (\ k → Hopf (test0To4 k i0 k)) i0 base1))
--                      (helix (primTransp (\ k → Hopf (test0To4 k i1 k)) i0 base1))
-- problempath j = helix (primTransp (\ k → Hopf (test0To4 k j k)) i0 base1)
