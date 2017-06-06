{-# OPTIONS --cubical #-}
module Category where

open import PathPrelude

-- Functor
record Func {ℓ} : Set (ℓ-suc ℓ) where
  field
    map      : Set ℓ → Set ℓ
    fmap     : {A B : Set ℓ} → (A → B) → map A → map B
    presId   : (A : Set ℓ) → fmap (idFun A) ≡ idFun (map A)
    presComp : {A B C : Set ℓ} → (f : A → B) → (g : B → C) →
                 fmap (g ∘ f) ≡ (fmap g) ∘ (fmap f)

-- Functor Path
record Func≡ {ℓ} : Set (ℓ-suc ℓ) where
  field F G : Func {ℓ}
  module L = Func F
  module R = Func G

  field
    map≡      : (A : Set ℓ) →
      Path
      (L.map A)        (R.map A)
    fmap≡     : {A B : Set ℓ} → (f : A → B) →
      PathP (λ i → map≡ A i → map≡ B i)
      (L.fmap f)       (R.fmap f)
    presId≡   : (A : Set ℓ) →
      PathP (λ i → fmap≡ (idFun A) i ≡ idFun (map≡ A i))
      (L.presId A)     (R.presId A)
    presComp≡ : {A B C : Set ℓ} → (f : A → B) → (g : B → C) →
      PathP (λ i → fmap≡ (g ∘ f) i ≡ (fmap≡ g) i ∘ (fmap≡ f) i)
      (L.presComp f g) (R.presComp f g)

  path : F ≡ G
  path i = record { map      = λ A   → map≡      A   i
                  ; fmap     = λ f   → fmap≡     f   i
                  ; presId   = λ A   → presId≡   A   i
                  ; presComp = λ f g → presComp≡ f g i }

idᶠ : ∀{ℓ} → Func {ℓ}
idᶠ = record { map      = idFun (Set _)
             ; fmap     = λ {A B} → idFun (A → B)
             ; presId   = λ _ → refl
             ; presComp = λ _ _ → refl }

-- Composition of Functor
infixr 45 _∘ᶠ_
_∘ᶠ_ : ∀{ℓ} → Func {ℓ} → Func {ℓ} → Func {ℓ}
G ∘ᶠ F = record
  { map      = G.map ∘ F.map
  ; fmap     = G.fmap ∘ F.fmap
  ; presId   = λ A → trans (cong G.fmap (F.presId A)) (G.presId _)
  ; presComp = λ f g → trans (cong G.fmap (F.presComp f g)) (G.presComp _ _)
  } where module F = Func F
          module G = Func G

idᶠLeft : ∀{ℓ}{F : Func {ℓ}} → idᶠ ∘ᶠ F ≡ F
idᶠLeft {ℓ} {F} = Func≡.path r where
  module L = Func (idᶠ ∘ᶠ F)
  module R = Func F
  map≡ : L.map ≡ R.map
  map≡ = funExt (λ _ → refl)
  r = record { F         = idᶠ ∘ᶠ F
             ; G         = F
             ; map≡      = λ A → refl
             ; fmap≡     = λ f → funExt λ _ → refl
             ; presId≡   = λ A → {!!}
             ; presComp≡ = λ f g → {!!}
             }

-- idᶠRight : ∀{ℓ}{F : Func {ℓ}} → F ∘ᶠ idᶠ ≡ F
-- idᶠRight {ℓ} {F} = TODO


-- Natural Transformation
infixr 40 _⇒ⁿ_
record _⇒ⁿ_ {ℓ} (F G : Func {ℓ}) : Set (ℓ-suc ℓ) where
  module F = Func F
  module G = Func G
  field
    map : (A : Set ℓ) → F.map A → G.map A
    nat : ∀{A B} → (f : A → B) → (G.fmap f) ∘ (map A) ≡ (map B) ∘ (F.fmap f)

-- Natural Transformation identity over Functor
idⁿ : ∀{ℓ} → (F : Func {ℓ}) → F ⇒ⁿ F
idⁿ F = record { map = λ A → idFun (Func.map F A)
               ; nat = λ _ → refl }

-- Vertical Composition of Natural Transformation
infixr 35 _∘ⁿ_
_∘ⁿ_ : ∀{ℓ}{F G H : Func {ℓ}} → G ⇒ⁿ H → F ⇒ⁿ G → F ⇒ⁿ H
_∘ⁿ_ {F = F} {H = H} β α = record { map = λ A → β.map A ∘ α.map A
                                  ; nat = nat } where
  module F = Func F
  module H = Func H
  module α = _⇒ⁿ_ α
  module β = _⇒ⁿ_ β
  nat : ∀{A B} → (f : A → B) → H.fmap f ∘ (β.map A ∘ α.map A)
                            ≡ (β.map B ∘ α.map B) ∘ F.fmap f
  nat {A} {B} f = trans (λ i → β.nat f i ∘ α.map A) (λ i → β.map B ∘ α.nat f i)


-- Horizontal Composition of Natural Transformation
infixr 35 _⋆ⁿ_
_⋆ⁿ_ : ∀{ℓ}{F F' G G' : Func {ℓ}} → F ⇒ⁿ G → F' ⇒ⁿ G' → (F' ∘ᶠ F) ⇒ⁿ (G' ∘ᶠ G)
_⋆ⁿ_ {ℓ} {F} {F'} {G} {G'} α β = record { map = map ; nat = nat } where
  module F  = Func F
  module F' = Func F'
  module G  = Func G
  module G' = Func G'
  module F'∘F = Func (F' ∘ᶠ F)
  module G'∘G = Func (G' ∘ᶠ G)
  module α  = _⇒ⁿ_ α
  module β  = _⇒ⁿ_ β
  map : (A : Set ℓ) → F'∘F.map A → G'∘G.map A
  map A = β.map (G.map A) ∘ F'.fmap (α.map A)
  nat : ∀{A B} → (f : A → B) → G'∘G.fmap f ∘ map A ≡ map B ∘ F'∘F.fmap f
  nat {A} {B} f = trans (λ i → β.nat (G.fmap f) i ∘ F'.fmap (α.map A))
    (cong (β.map (G.map B) ∘_) (trans (sym (F'.presComp (α.map A) (G.fmap f)))
      (trans (cong F'.fmap (α.nat f)) (F'.presComp (F.fmap f) (α.map B)))))
