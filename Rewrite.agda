{-# OPTIONS --rewriting #-}
module Rewrite where

postulate
  Rewrite : ∀ {ℓ} {A : Set ℓ} → A → A → Set

{-# BUILTIN REWRITE Rewrite #-}
