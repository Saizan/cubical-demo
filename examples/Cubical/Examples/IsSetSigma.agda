{-# OPTIONS --cubical #-}
module Cubical.Examples.IsSetSigma where
open import Cubical.PathPrelude
open import Cubical.Prelude
open import Cubical.Comp


-- My first attempt at a direct style proof.

-- Since "lemPropF" is quite helpful in the proof of propSig, I tried
-- to have a similar lemma but for isSet.
-- However my lemSetF didn't help enough, so I tried a different approach below.
module FirstAttempt {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where

  -- here the endpoints b0 and b1 live over a line in A, but p and q
  -- are still of the same type, so it's not as general as it could.
  -- Which means we still have to do the compositions in the proof of setSigF.
  isSetF = (x y : A) → (l : x ≡ y) → {b0 : B x}{b1 : B y} → (p q : PathP (\ i → B (l i)) b0 b1) →  p ≡ q

  lemSetF : (sB : (x : A)→ isSet (B x)) → isSetF
  lemSetF sB x = pathJ (λ y z →
                       {b0 : B x} {b1 : B y} (p q : PathP (λ i → B (z i)) b0 b1) → p ≡ q)
                       (sB x _ _)

  setSigF : {sA : isSet A}{sB : isSetF}(t u : Σ A B)→ isProp (t ≡ u)
  setSigF {sA} {sB} t u p q i j = fsteq i j
                                , sB (t .fst) (u .fst)
                                   (fsteq i)
                                   (comp (\ k → PathP (\ j' → B (fsteq (k   ∧ i) j')) (t .snd) (u .snd)) (\ {k (i = i0) → p'}) (inc p'))
                                   (comp (\ k → PathP (\ j' → B (fsteq (~ k ∨ i) j')) (t .snd) (u .snd)) (\ {k (i = i1) → q'}) (inc q'))
                                   i j
    where
       p' : PathP (λ z → B (p z .fst)) (t .snd) (u .snd)
       p' = \ i → p i .snd
       q' : PathP _ _ _
       q' = \ i → q i .snd
       fsteq = sA (t .fst) (u .fst) (\ i → p i .fst) (\ i → q i .fst)

  setSig : {sA : isSet A}{sB : (a : A) → isSet (B a)}(t u : Σ A B)→ isProp(t ≡ u)
  setSig {sA} {sB} = setSigF {sA} {lemSetF sB}



------------------------------------------------------------------------------------
-- Here's the second attempt.

-- isSet A is equivalent to being able to fill the interior of any
-- complete square perimeter in A.
Square : ∀ {ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A}
          (u : a0 ≡ a1) (v : b0 ≡ b1) (r0 : a0 ≡ b0) (r1 : a1 ≡ b1) → Set ℓ
Square {A = A} u v r0 r1 = PathP (λ i → (u i ≡ v i)) r0 r1

hasSquares : ∀ {ℓ} (A : Set ℓ) → Set _
hasSquares A = ∀ {a0 a1 b0 b1 : A} p0 p1 q0 q1 → Square {a0 = a0} {a1} {b0} {b1} p0 p1 q0 q1

square-isSet : ∀ {ℓ} {A : Set ℓ} (sqA : hasSquares A) → isSet A
square-isSet sqA x y p q i j = sqA refl refl p q i j

isSet-square : ∀ {ℓ} {A : Set ℓ} → isSet A → hasSquares A
isSet-square {_} {A} sA {a0} p0 p1 q0 q1 = pathJ
                                             (λ a1 p2 →
                                                ∀ {b0} (b1 : A) p3 q2 q3 →
                                                Square {_} {A} {a0} {a1} {b0} {b1} p2 p3 q2 q3)
                                             (pathJ _ (sA a0 _)) _ p0 _ (λ z → p1 z) q0 q1


-- Heterogeneous squares.
SquareP : ∀ {l} (A : I → I → Set l) {a0 a1 b0 b1}
          → (u : PathP (\ i → A i i0) a0 a1) (v : PathP (\ i → A i i1) b0 b1)
            (r0 : PathP (A i0) a0 b0)        (r1 : PathP (A i1) a1 b1) → Set l
SquareP A u v r0 r1 = PathP (\ i → PathP (\ j → A i j) (u i) (v i)) r0 r1

-- For a type family "B : A → Set ℓ'" we want to be able to fill heterogeneous squares.
hasSquaresP : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') (α : I → I → A) → Set _
hasSquaresP {A = A} B α = ∀ {a0 a1 b0 b1} u v r0 r1 → SquareP (\ i j → B (α i j)) {a0} {a1} {b0} {b1} u v r0 r1

-- J for squares. Follows because a square can be contracted to one of its corners.
contrSquare : ∀ {ℓ} {A : Set ℓ} → (α : I → I → A) → I → I → I → A
contrSquare α k i j = α (i ∧ k) (j ∧ k)

squareJ : ∀ {ℓ ℓ'} {A : Set ℓ} (B : (I → I → A) → Set ℓ') (α : I → I → A) → B (\ _ _ → α i0 i0)  → B α
squareJ {A = A} B α b = transp (\ k → B (\ i j → contrSquare α k i j)) b


module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where

  lemSquaresF : ((x : A) → hasSquares (B x)) → (∀ α → hasSquaresP B α)
  lemSquaresF sB α = squareJ (hasSquaresP B) α (sB (α i0 i0))

  -- Finally the actual proof becomes straightforward because the premises are general enough.
  setSigSq : {sA : hasSquares A}{sB : ((x : A) → hasSquares (B x))} → hasSquares (Σ A B)
  setSigSq {sA} {sB} p0 p1 q0 q1 i j = sA (cong fst p0) (cong fst p1) (cong fst q0) (cong fst q1) i j
                                     , lemSquaresF sB
                                         (λ i j → sA (cong fst p0) (cong fst p1) (cong fst q0) (cong fst q1) i j)
                                         (\ i → p0 i .snd) (\ i → p1 i .snd) (\ i → q0 i .snd) (\ i → q1 i .snd) i j

  setSig : {sA : isSet A}{sB : ((x : A) → isSet (B x))} → isSet (Σ A B)
  setSig {sA} {sB} = square-isSet (setSigSq {isSet-square sA} {\ x → isSet-square (sB x)})
