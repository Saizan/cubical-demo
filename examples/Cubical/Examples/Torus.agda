{-# OPTIONS --cubical #-}
module Cubical.Examples.Torus where

open import Cubical.Examples.Circle
open import Cubical.FromStdLib
open import Cubical.PathPrelude

SquareP : ∀ {l} (A : I → I → Set l) {a0 a1 b0 b1}
          → (u : PathP (\ i → A i i0) a0 a1) (v : PathP (\ i → A i i1) b0 b1)
            (r0 : PathP (A i0) a0 b0)        (r1 : PathP (A i1) a1 b1) → Set l
SquareP A u v r0 r1 = PathP (\ i → PathP (\ j → A i j) (u i) (v i)) r0 r1

data Torus : Set where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : Square line1 line1 line2 line2

module _    (Torusₘ : Torus → Set)
            (pointₘ  : Torusₘ point)
            (line1ₘ  : PathP (\ i → Torusₘ (line1 i)) pointₘ pointₘ)
            (line2ₘ  : PathP (\ i → Torusₘ (line2 i)) pointₘ pointₘ)
            (squareₘ : SquareP (\ i j → Torusₘ (square i j)) line1ₘ line1ₘ line2ₘ line2ₘ) where

  elimTorus : ∀ x → Torusₘ x
  elimTorus point        = pointₘ
  elimTorus (line1 i)    = line1ₘ i
  elimTorus (line2 i)    = line2ₘ i
  elimTorus (square i j) = squareₘ i j


t2c : Torus → S¹ × S¹
t2c point        = base   , base
t2c (line1 i)    = loop i , base
t2c (line2 j)    = base   , loop j
t2c (square i j) = loop i , loop j

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (base   , loop j) = line2 j
c2t (loop i , base)   = line1 i
c2t (loop i , loop j) = square i j

t2c-c2t : ∀ t → c2t (t2c t) ≡ t
t2c-c2t point        = refl
t2c-c2t (line1 i)    = refl
t2c-c2t (line2 j)    = refl
t2c-c2t (square i j) = refl

c2t-t2c : ∀ p → t2c (c2t p) ≡ p
c2t-t2c (base   , base)   = refl
c2t-t2c (base   , loop j) = refl
c2t-t2c (loop i , base)   = refl
c2t-t2c (loop i , loop j) = refl
