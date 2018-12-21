{-# OPTIONS --cubical #-}
module Cubical.Examples.OTTU where

open import Cubical.PathPrelude
open import Cubical.FromStdLib

open import Cubical.Examples.Cube

record ⊤ : Set where


data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) → (B x → W A B) → W A B

mutual
  data U : Set where
    `Π `Σ `W : (A : U) → (B : El A → U) → U
    `⊥ `⊤ `2 : U

  El : U → Set
  El (`Π A B) = (x : El A) → (El (B x))
  El (`Σ A B) = Σ (El A) (λ x → El (B x))
  El (`W A B) = W (El A) (λ x → El (B x))
  El `⊥ = ⊥
  El `⊤ = ⊤
  El `2 = Bool

-- -- "one-step" reduction of composition of Π.
-- test-Π : ∀ φ (A : I → Partial φ U)
--          → (B : (i : I) → PartialP φ λ o → (x : El (A i o)) → U)
--          → (A0 : U) (B0 : El A0 → U)
--          → unsafeComp (λ i → U) φ (λ i o → `Π (A i o) (B i o)) (`Π A0 B0)
--          ≡ `Π (unsafeComp (λ i → U) φ A A0)
--               (unsafeComp (λ i → El (fill (λ i → U) φ A A0 i) → U)
--                           φ (λ i → λ { (φ = i1) → B i itIsOne }) B0)
-- test-Π = λ φ A B A0 B0 → refl

-- -- when starting from a constant system
-- -- we get constant systems in the one-step reduction.
-- test-Π-const : ∀ φ (A' : Partial φ U) (let A = λ (i : I) → A')
--          → (B' : PartialP φ λ o → (x : El (A' o)) → U) (let B  = λ (i : I) → B')
--          → (A0 : U) (B0 : El A0 → U)
--          → unsafeComp (λ i → U) φ (λ i o → `Π (A i o) (B i o)) (`Π A0 B0)
--            ≡ `Π (unsafeComp (λ i → U) φ (λ _ → A') A0)
--                 (unsafeComp (λ i → El (fill (λ i → U) φ (λ _ → A') A0 i) → U)
--                             φ (λ i → λ { (φ = i1) → B' itIsOne }) B0)
-- test-Π-const = λ φ A' B' A0 B0 → refl

-- test-Σ : ∀ φ (A : I → Partial φ U)
--          → (B : (i : I) → PartialP φ λ o → (x : El (A i o)) → U)
--          → (A0 : U) (B0 : El A0 → U)
--          → unsafeComp (λ i → U) φ (λ i o → `Σ (A i o) (B i o)) (`Σ A0 B0)
--          ≡ `Σ (unsafeComp (λ i → U) φ A A0)
--               (unsafeComp (λ i → El (fill (λ i → U) φ A A0 i) → U)
--                           φ (λ i → λ { (φ = i1) → B i itIsOne }) B0)
-- test-Σ = λ φ A B A0 B0 → refl

-- test-W : ∀ φ (A : I → Partial φ U)
--          → (B : (i : I) → PartialP φ λ o → (x : El (A i o)) → U)
--          → (A0 : U) (B0 : El A0 → U)
--          → unsafeComp (λ i → U) φ (λ i o → `W (A i o) (B i o)) (`W A0 B0)
--          ≡ `W (unsafeComp (λ i → U) φ A A0)
--               (unsafeComp (λ i → El (fill (λ i → U) φ A A0 i) → U)
--                           φ (λ i → λ { (φ = i1) → B i itIsOne }) B0)
-- test-W = λ φ A B A0 B0 → refl
