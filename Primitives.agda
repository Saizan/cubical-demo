{-# OPTIONS --cubical #-}
module Primitives where



module Postulates where
  open import Agda.Primitive public renaming (isOneEmpty to empty)

  postulate
    Path : ∀ {a} {A : Set a} → A → A → Set a
    PathP : ∀ {a} → (A : I → Set a) → A i0 → A i1 → Set a

  {-# BUILTIN PATH         Path     #-}
  {-# BUILTIN PATHP        PathP     #-}

  primitive
    primPathApply : ∀ {a} {A : Set a} {x y : A} → Path x y → I → A
    primPathPApply : ∀ {a} → {A : I → Set a} → ∀ {x y} → PathP A x y → (i : I) → A i

  {-# BUILTIN RESTRICT    Restrict #-}
  {-# BUILTIN PSINGL      r[_]     #-}


  postulate
    Id : ∀ {a} {A : Set a} → A → A → Set a

  {-# BUILTIN ID           Id       #-}
  {-# BUILTIN CONID        conid    #-}

  primitive
    primDepIMin : _
    primIdFace : _
    primIdPath : _

  primitive
    primIdJ : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Id x y → Set p) → P x (conid i1 (\ i -> x)) → ∀ {y} (p : Id x y) → P y p

  {-# BUILTIN SUB Sub #-}

  postulate
    inc : ∀ {a} {A : Set a} {φ} (x : A) → Sub {A = A} φ (\ _ → x)

  {-# BUILTIN SUBIN inc #-}

  primitive
    primSubOut : {a : Level} {A : Set a} {φ : I} {u : Partial A φ} → Sub φ u → A


open Postulates public renaming (primPathApply to _∙_; primIMin to _∧_; primIMax to _∨_; primINeg to ~_
                                ; primPFrom1 to p[_]
                                ; primIdJ to J
                                ; primSubOut to ouc
                                )

module Unsafe' (dummy : Set₁) = Postulates

open Unsafe' Set public using () renaming (conid to unsafeConId; primComp to unsafeComp)


unsafePOr = Unsafe'.primPOr Set

_≡_ = Path
