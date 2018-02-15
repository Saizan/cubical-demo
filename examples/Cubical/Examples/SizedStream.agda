{-# OPTIONS --cubical #-}
module Cubical.Examples.SizedStream where

open import Cubical.PathPrelude
open import Cubical.FromStdLib using (_×_)
open import Agda.Builtin.Size

record Stream (A : Set) (i : Size) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : ∀ {j : Size< i} → Stream A j

open Stream

antitone : ∀ {A : Set} → (i : Size) (xs ys : Stream A i) → (j : Size< i) →
  Path xs ys → Path {A = Stream A j} xs ys
antitone i xs ys j eq k = eq k
