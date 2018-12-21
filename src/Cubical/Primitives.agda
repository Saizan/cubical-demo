{-# OPTIONS --cubical #-}
module Cubical.Primitives where

module Postulates where
  open import Agda.Primitive.Cubical public
  open import Agda.Builtin.Cubical.Path public
  open import Agda.Builtin.Cubical.Id public
  open import Agda.Builtin.Cubical.Sub public

  infix 4 _[_≡_]
  _[_≡_] : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
  _[_≡_] = PathP

  Path = _≡_

open Postulates public renaming
  ( primIMin       to _∧_   ; primIMax       to _∨_  ; primINeg   to ~_
  ; isOneEmpty     to empty ; primIdJ        to J    ; primSubOut to ouc )
