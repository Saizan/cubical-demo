module FromStdLib where

open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero ; lsuc  to ℓ-suc ; _⊔_  to ℓ-max )

open import Agda.Builtin.List public

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

data ⊥ : Set where

⊥-elim : ∀ {l} {A : Set l} → ⊥ → A
⊥-elim ()

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥


data Bool : Set where
  true false : Bool

record Σ {a b} (A : Set a) (B : A → Set b) : Set (ℓ-max a b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (ℓ-max a b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixr 4 _,_
infixr 2 _×_

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (ℓ-max a b)
A × B = Σ[ x ∈ A ] B

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

idFun : ∀ {ℓ} → (A : Set ℓ) → A → A
idFun A x = x
