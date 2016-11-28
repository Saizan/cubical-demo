{-# OPTIONS --cubical #-}
module SizedStream where

open import Data.Product using (_×_)
open import PathPrelude
open import Size

record Stream (A : Set) (i : Size) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : ∀ {j : Size< i} → Stream A j

open Stream

antitone : ∀ {A : Set} → (i : Size) (xs ys : Stream A i) → (j : Size< i) → Path xs ys → Path {A = Stream A j} xs ys
antitone i xs ys j eq k = eq k
