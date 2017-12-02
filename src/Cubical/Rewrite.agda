{-# OPTIONS --rewriting #-}
module Cubical.Rewrite where

postulate
  Rewrite : ∀ {ℓ} {A : Set ℓ} → A → A → Set

{-# BUILTIN REWRITE Rewrite #-}
