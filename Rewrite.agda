{-# OPTIONS --rewriting #-}
module Rewrite where



postulate
  Rewrite : ∀ {l} {A : Set l} → A → A → Set

{-# BUILTIN REWRITE Rewrite #-}
