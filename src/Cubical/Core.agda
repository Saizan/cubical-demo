{-# OPTIONS --cubical #-}
module Cubical.Core where

open import Agda.Primitive.Cubical public renaming
  ( primIMin       to _∧_  -- I → I → I
  ; primIMax       to _∨_ -- I → I → I
  ; primINeg       to ~_
  -- TODO change to emptySystem in src/full
  ; isOneEmpty     to empty
  ; primComp to comp
  ; primHComp to hcomp
  ; primTransp to transp
  ; itIsOne    to 1=1
  )
open import Agda.Builtin.Cubical.Path public

-- This files document the Cubical Agda primitives.
-- The primitives themselves are bound by the agda files imported above.

-- * The Interval
-- I : Setω

-- Endpoints, Connections, Reversal
-- i0 i1   : I
-- _∧_ _∨_ : I → I → I
-- ~_      : I → I



-- * Dependent path type. (Path over Path)

-- Introduced with lambda abstraction and eliminated with application,
-- just like function types.

-- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

infix 4 _[_≡_]

_[_≡_] : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
_[_≡_] = PathP

-- Non dependent path type.
-- PathP (\ i → A) x y gets printed as x ≡ y when A does not mention i.
--  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
--  _≡_ {A = A} = PathP (λ _ → A)


-- * @IsOne r@ represents the constraint "r = i1".
-- Often we will use "φ" for elements of I, when we intend to use them
-- with IsOne (or Partial[P]).
-- IsOne : I → Set

-- i1 is indeed equal to i1.
-- 1=1 : IsOne i1


-- * Types of partial elements, and their dependent version.

-- "Partial φ A" is a special version of "IsOne φ → A" with a more
-- extensional judgmental equality.
-- "PartialP φ A" allows "A" to be defined only on "φ".

-- Partial : ∀ {l} → I → Set l → Setω
-- PartialP : ∀ {l} → (φ : I) → Partial (Set l) φ → Setω

-- Partial elements are introduced by pattern matching with (r = i0) or (r = i1) constraints, like so:

private
  sys : ∀ i → Partial (i ∨ ~ i) Set₁
  sys i (i = i0) = Set
  sys i (i = i1) = Set → Set

-- It also works with pattern matching lambdas. (TODO link pattern matching lambda docs)
  sys' : ∀ i → Partial (i ∨ ~ i) Set₁
  sys' i = \ { (i = i0) → Set
             ; (i = i1) → Set → Set
             }

-- When the cases overlap they must agree.
  sys2 : ∀ i j → Partial (i ∨ (i ∧ j)) Set₁
  sys2 i j = \ { (i = i1)          → Set
               ; (i = i1) (j = i1) → Set
               }

  sys3 : Partial i0 Set₁
  sys3 = \ { () }





-- * Composition operation according to [CCHM 18].
-- When calling "comp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- comp : ∀ {l} (A : (i : I) → Set (l i)) (φ : I) (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1


-- * Generalized transport and homogeneous composition [CHM 18].
-- Used to support Higher Inductive Types.

-- When calling "transp A φ a" Agda makes sure that "A" is constant on "φ".
-- transp : ∀ {l} (A : (i : I) → Set (l i)) (φ : I) (a : A i0) → A i1

-- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- hcomp : ∀ {l} {A : Set l} {φ : I} (u : I → Partial φ A) (a : A) → A
