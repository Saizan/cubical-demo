{-# OPTIONS --cubical #-}

module FromStdLib where

open import Data.Product public
  using    ( Σ ; _,_ ; Σ-syntax ; _×_ ; curry ; uncurry)
  renaming ( proj₁ to fst ; proj₂ to snd )

open import Function public
  using    ( _∘_ ; flip )

idFun : ∀{ℓ} → (A : Set ℓ) → A → A
idFun A x = x

open import Level public
  using    ( Level ; Lift ; lift )
  renaming ( zero to ℓ-zero ; suc  to ℓ-suc ; _⊔_  to ℓ-max )
