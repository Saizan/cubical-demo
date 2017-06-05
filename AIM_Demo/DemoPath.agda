{-# OPTIONS --cubical #-}
module AIM_Demo.DemoPath where

open import Primitives


refl : ∀ {a} {A : Set a} {x : A} → Path x x
refl {x = d} = λ i → d

-- ~ : I → I
-- ~ i0 ≡ i1
-- ~ i1 ≡ i0
-- ~ (~ i) ≡ i

sym : ∀ {a} {A : Set a} → {x y : A} → Path x y → Path y x
sym p = λ i → p (~ i)



-- _≡_ = Path

test-sym : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → sym (sym p) ≡ p
test-sym p = refl



test-0 : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → p i0 ≡ x
test-0 p = refl

test-1 : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → p i1 ≡ y
test-1 p = refl



eta-expand : ∀ {a} {A : Set a} {x y : A} → (p : Path x y) -> Path x y
eta-expand p = λ z → p z


eta-eq : ∀ {a} {A : Set a} {x y : A} → (p : Path x y) -> Path p (eta-expand p)
eta-eq p = refl




-- primComp : ∀ {a} (A : (i : I) → Set (a i)) (φ : I) → (∀ i → Partial (A i) φ) → (a : A i0) → A i1

-- ("Partial A φ" is something like "(φ = i1) → A")


pathJ : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Path x y → Set p) → P x refl →
        ∀ y (p : Path x y) → P y p
pathJ P d _ p = primComp (λ i → P (p i) (\ j → p (i ∧ j))) i0 (\ _ → empty) d


test-primComp : ∀ {a} (A : Set a) {x y : A} (p : Path x y) → primComp (\ _ → A) i1 (\ j _ → p j) x ≡ y
test-primComp A p = refl

pathJprop : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Path x y → Set p) → (d : P x ((\ i -> x))) →
            pathJ P d _ refl ≡ d
pathJprop {x = x} P d = \ i → primComp (λ _ → P x refl) i (\ { j (i = i1) → d }) d






fun-ext : ∀ {a b} {A : Set a} {B : A → Set b} → {f g : (x : A) → B x}
          → (∀ x → Path (f x) (g x)) → Path f g
fun-ext p = λ i → \ x → p x i

-- p x i0 = f x
-- p x i1 = g x




-- conid : {a : Level} {A : Set a} {x y : A} → (φ : I) → Path x y → Id x y

reflId : ∀ {a} {A : Set a}{x : A} → Id x x
reflId {x = x} = conid i1 (λ _ → x)

Jdef : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Id x y → Set p) → (d : P x reflId) → J P d reflId ≡ d
Jdef P d = refl

fromPath : ∀ {A : Set}{x y : A} → Path x y -> Id x y
fromPath p = conid i0 (\ i → p i)
