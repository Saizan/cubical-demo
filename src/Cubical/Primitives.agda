{-# OPTIONS --cubical #-}
module Cubical.Primitives where

module Postulates where
  open import Agda.Primitive.Cubical public

  postulate
    Path' : ∀ {ℓ} {A :     Set ℓ} → A    → A    → Set ℓ
    PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

  {-# BUILTIN PATH         Path'     #-}
  {-# BUILTIN PATHP        PathP     #-}

  infix 4 _≡_
  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  _≡_ {A = A} = PathP (λ _ → A)

  Path = _≡_

  primitive
    primPathApply  : ∀ {ℓ} {A :     Set ℓ} {x y} → Path'   x y →      I →  A
    primPathPApply : ∀ {ℓ} {A : I → Set ℓ} {x y} → PathP A x y → (i : I) → A i

  postulate
    Id : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ

  {-# BUILTIN ID           Id       #-}
  {-# BUILTIN CONID        conid    #-}

  primitive
    primDepIMin : _
    primIdFace : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
    primIdPath : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → Path' x y

  primitive
    primIdJ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ') →
                P x (conid i1 (λ i → x)) → ∀ {y} (p : Id x y) → P y p

  {-# BUILTIN SUB Sub #-}

  postulate
    inc : ∀ {ℓ} {A : Set ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

  {-# BUILTIN SUBIN inc #-}

  primitive
    primSubOut : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial A φ} → Sub _ φ u → A


open Postulates public renaming
  ( primPFrom1 to p[_]
  ; primIMin       to _∧_   ; primIMax       to _∨_  ; primINeg   to ~_
  ; isOneEmpty     to empty ; primIdJ        to J    ; primSubOut to ouc )


module Unsafe' (dummy : Set₁) = Postulates
unsafeComp = Unsafe'.primComp Set
unsafePOr  = Unsafe'.primPOr  Set
