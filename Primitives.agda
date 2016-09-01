{-# OPTIONS --cubical #-}
module Primitives where

module Postulates where

  {-# BUILTIN INTERVAL I    #-} -- I : Setω

  postulate
    i0 i1 : I
  {-# BUILTIN IZERO    i0   #-}
  {-# BUILTIN IONE     i1   #-}

  infix 30 primINeg

  primitive
      primIMin : I → I → I
      primIMax : I → I → I
      primINeg : I → I

  postulate
    Path : ∀ {a} {A : Set a} → A → A → Set a
    PathP : ∀ {a} → (A : I → Set a) → A i0 → A i1 → Set a


  {-# BUILTIN PATH         Path     #-}
  {-# BUILTIN PATHP        PathP     #-}

  primitive
    primPathApply : ∀ {a} {A : Set a} {x y : A} → Path x y → I → A
    primPathPApply : ∀ {a} → {A : I → Set a} → ∀ {x y} → PathP A x y → (i : I) → A i



  {-# BUILTIN ISONE        IsOne #-} -- IsOne : I → Setω

  postulate
    itIsOne : IsOne i1
    IsOne1  : ∀ i j → IsOne i → IsOne (primIMax i j)
    IsOne2  : ∀ i j → IsOne j → IsOne (primIMax i j)

  {-# BUILTIN ITISONE      itIsOne  #-}
  {-# BUILTIN ISONE1       IsOne1   #-}
  {-# BUILTIN ISONE2       IsOne2   #-}
  {-# BUILTIN PARTIAL      Partial  #-}
  {-# BUILTIN PARTIALP     PartialP #-}

  postulate
    empty : ∀ {a} {A : Set a} → Partial A i0

  {-# BUILTIN RESTRICT    Restrict #-}
  {-# BUILTIN PSINGL      r[_]     #-}

  primitive
    primPFrom1 : ∀ {a} {A : I → Set a} → A i1 → ∀ i j → Partial (A (primIMax i j)) i
    primPOr : ∀ {a} (i j : I) {A : Partial (Set a) (primIMax i j)} → PartialP i (λ z → A (IsOne1 i j z)) → PartialP j (λ z → A (IsOne2 i j z))
                 → PartialP (primIMax i j) A

  syntax primPOr p q u t = [ p ↦ u , q ↦ t ]



  primitive
    primComp : ∀ {a} (A : (i : I) → Set (a i)) (φ : I) → (∀ i → Partial (A i) φ) → (a : A i0) → A i1



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
