{-# OPTIONS --cubical #-}

module Stream where
open import Data.Product using (_×_)
open import PathPrelude


record Stream (A : Set) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

open Stream

mapS : ∀ {A B} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)

mapS-id : ∀ {A} {xs : Stream A} → mapS (\ x → x) xs ≡ xs
head (mapS-id {xs = xs} i) = head xs
tail (mapS-id {xs = xs} i) = mapS-id {xs = tail xs} i


Stream-η : ∀ {A} {xs : Stream A} → xs ≡ (head xs , tail xs)
head (Stream-η {A} {xs} i) = head xs
tail (Stream-η {A} {xs} i) = tail xs


elimS : ∀ {A} (P : Stream A → Set) → (∀ x xs → P (x , xs)) → (xs : Stream A) → P xs
elimS P c xs = primComp (\ i → P (Stream-η {xs = xs} (~ i))) i0 (\ _ → empty) (c (head xs) (tail xs))


module Equality≅Bisimulation where
  record _≈_ {A : Set} (x y : Stream A) : Set where
    coinductive
    field
      ≈head : head x ≡ head y
      ≈tail : tail x ≈ tail y

  open _≈_

  bisim : {A : Set} → {x y : Stream A} → x ≈ y → x ≡ y
  head (bisim x≈y i) = ≈head x≈y i
  tail (bisim x≈y i) = bisim (≈tail x≈y) i

  misib : {A : Set} → {x y : Stream A} → x ≡ y → x ≈ y
  ≈head (misib p) = \ i → head (p i)
  ≈tail (misib p) = misib (\ i → tail (p i))

  iso1 : {A : Set} → {x y : Stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
  head (iso1 p i j) = head (p j)
  tail (iso1 p i j) = iso1 (\ i → tail (p i)) i j

  iso2 : {A : Set} → {x y : Stream A} → (p : x ≈ y) → misib (bisim p) ≡ p
  ≈head (iso2 p i) = ≈head p
  ≈tail (iso2 p i) = iso2 (≈tail p) i


  -- misib can be implemented by transport as well.
  refl≈ : {A : Set} {x : Stream A} → x ≈ x
  ≈head refl≈ = refl
  ≈tail refl≈ = refl≈

  cast : ∀ {A : Set} {x y : Stream A} (p : x ≡ y) → x ≈ y
  cast {A} {x} {y} p = primComp (\ i → x ≈ p i) i0 (\ i → empty) refl≈

  fill-id : ∀ {A : Set} {x} (y : A) (q : x ≡ y) → (\ i → fill (\ i → A) i (\ i' → (λ _ → q i')) x i) ≡ q
  fill-id {A} {x} = pathJ _ (\ j → \ i →  fill (\ _ → A) (i ∨ ~ i) (\ _ → \ _ → x) x (~ j))

  misib-transp : ∀ {A : Set} {x y : Stream A} (p : x ≡ y) → cast p ≡ misib p
  ≈head (misib-transp p i) = fill-id _ (\ i → head (p i)) i
  ≈tail (misib-transp p i) = misib-transp (\ i → tail (p i)) i



module Stream≅Nat→ {A : Set} where

  open import Data.Nat

  lookup : Stream A → ℕ → A
  lookup xs zero = head xs
  lookup xs (suc n) = lookup (tail xs) n

  tabulate : (ℕ → A) → Stream A
  head (tabulate f) = f 0
  tail (tabulate f) = tabulate (\ n → f (suc n))


  lookup∘tabulate : (\ (x : _ → _) → lookup (tabulate x)) ≡ (\ x → x)
  lookup∘tabulate i f zero = f zero
  lookup∘tabulate i f (suc n) = lookup∘tabulate i (\ n → f (suc n)) n


  tabulate∘lookup : (\ (x : Stream _) → tabulate (lookup x)) ≡ (\ x → x)
  head (tabulate∘lookup i xs) = head xs
  tail (tabulate∘lookup i xs) = tabulate∘lookup i (tail xs)

  open import GradLemma

  Stream≡Nat→ : Stream A ≡ (ℕ → A)
  Stream≡Nat→ = isoToPath lookup tabulate
                          (\ f i → lookup∘tabulate i f) (\ xs i → tabulate∘lookup i xs)
