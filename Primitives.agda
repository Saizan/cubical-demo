{-# OPTIONS --cubical #-}
module Primitives where



module Postulates where
  open import Agda.Primitive public

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
    primIdJ : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Id x y → Set p) → P x (conid i1 (\ i -> x)) → ∀ {y} (p : Id x y) → P y p



open Postulates public renaming (primPathApply to _∙_; primIMin to _∧_; primIMax to _∨_; primINeg to ~_
                                ; primPFrom1 to p[_]
                                ; primIdJ to J
                                )

module Unsafe' (dummy : Set₁) = Postulates

open Unsafe' Set public using () renaming (conid to unsafeConId; primComp to unsafeComp)


unsafePOr = Unsafe'.primPOr Set

_≡_ = Path
