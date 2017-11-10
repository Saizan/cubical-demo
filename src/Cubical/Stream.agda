{-# OPTIONS --cubical #-}

module Cubical.Stream where
open import Data.Product using (_×_)
open import Cubical.PathPrelude


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


mapS-id : ∀ {A} {xs : Stream A} → mapS (λ x → x) xs ≡ xs
head (mapS-id {xs = xs} i) = head xs
tail (mapS-id {xs = xs} i) = mapS-id {xs = tail xs} i


Stream-η : ∀ {A} {xs : Stream A} → xs ≡ (head xs , tail xs)
head (Stream-η {A} {xs} i) = head xs
tail (Stream-η {A} {xs} i) = tail xs


elimS : ∀{A} (P : Stream A → Set) (c : ∀ x xs → P (x , xs)) (xs : Stream A) → P xs
elimS P c xs = transp (λ i → P (Stream-η {xs = xs} (~ i)))
                      (c (head xs) (tail xs))


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
  ≈head (misib p) = λ i → head (p i)
  ≈tail (misib p) = misib (λ i → tail (p i))

  iso1 : {A : Set} → {x y : Stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
  head (iso1 p i j) = head (p j)
  tail (iso1 p i j) = iso1 (λ i → tail (p i)) i j

  iso2 : {A : Set} → {x y : Stream A} → (p : x ≈ y) → misib (bisim p) ≡ p
  ≈head (iso2 p i) = ≈head p
  ≈tail (iso2 p i) = iso2 (≈tail p) i


  -- misib can be implemented by transport as well.
  refl≈ : {A : Set} {x : Stream A} → x ≈ x
  ≈head refl≈ = refl
  ≈tail refl≈ = refl≈

  cast : ∀ {A : Set} {x y : Stream A} (p : x ≡ y) → x ≈ y
  cast {A} {x} {y} p = transp (λ i → x ≈ p i) refl≈

  fillId : ∀ {A : Set} ({x} y : A) (q : x ≡ y) →
    (λ i → fill (λ i → A) i (λ i' → (λ _ → q i')) x i) ≡ q
  fillId {A}{x} = pathJ _ (λ j i → fill (λ _ → A) (i ∨ ~ i) (λ _ _ → x) x (~ j))

  misibTransp : ∀ {A : Set} {x y : Stream A} (p : x ≡ y) → cast p ≡ misib p
  ≈head (misibTransp p i) = fillId _ (λ i → head (p i)) i
  ≈tail (misibTransp p i) = misibTransp (λ i → tail (p i)) i



module Stream≅Nat→ {A : Set} where

  open import Data.Nat

  lookup : Stream A → ℕ → A
  lookup xs zero = head xs
  lookup xs (suc n) = lookup (tail xs) n

  tabulate : (ℕ → A) → Stream A
  head (tabulate f) = f 0
  tail (tabulate f) = tabulate (λ n → f (suc n))


  lookup∘tabulate : (λ (x : _ → _) → lookup (tabulate x)) ≡ (λ x → x)
  lookup∘tabulate i f zero = f zero
  lookup∘tabulate i f (suc n) = lookup∘tabulate i (λ n → f (suc n)) n


  tabulate∘lookup : (λ (x : Stream _) → tabulate (lookup x)) ≡ (λ x → x)
  head (tabulate∘lookup i xs) = head xs
  tail (tabulate∘lookup i xs) = tabulate∘lookup i (tail xs)

  open import Cubical.GradLemma

  Stream≡Nat→ : Stream A ≡ (ℕ → A)
  Stream≡Nat→ = isoToPath lookup tabulate
    (λ f i → lookup∘tabulate i f) (λ xs i → tabulate∘lookup i xs)
