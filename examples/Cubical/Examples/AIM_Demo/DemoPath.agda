{-# OPTIONS --cubical #-}
module Cubical.Examples.AIM_Demo.DemoPath where

open import Cubical.Primitives

-- I : Setω -- Interval type


-- Path {a} {A} x y ~~ {f : I → A | f i0 = x, f i1 = y}
refl : ∀ {a} {A : Set a} {x : A} → Path x x
refl {x = x} = λ _ → x











-- ~ : I → I
-- ~ i0 ≡ i1
-- ~ i1 ≡ i0
-- ~ (~ i) ≡ i

sym : ∀ {a} {A : Set a} → {x y : A} → Path x y → Path y x
sym p = λ i → p (~ i)

-- p i0 = x
-- p i1 = y

-- p (~ i0) = p i1 = y

-- _≡_ = Path

-- ~ (~ i) = i
test-sym : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → sym (sym p) ≡ p
test-sym p = refl



test-0 : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → p i0 ≡ x
test-0 p = refl

test-1 : ∀ {a} {A : Set a} → {x y : A} → (p : Path x y) → p i1 ≡ y
test-1 p = refl





eta-expand : ∀ {a} {A : Set a} {x y : A} → (p : Path x y) -> Path x y
eta-expand p = λ z → p z


eta-eq : ∀ {a} {A : Set a} {x y : A} → (p : Path x y)
         -> Path p (eta-expand p)
eta-eq p = refl









fun-ext : ∀ {a b} {A : Set a} {B : A → Set b} → {f g : (x : A) → B x}
          → (∀ x → Path {A = B x} (f x) (g x)) → Path f g
fun-ext p = λ i → λ x → p x i

--  p x i0 = f x
--  p x i1 = g x
-- -------------------------------------
--  (\ x → p x i0) = (\ x → f x) =η f
--  (\ x → p x i1) = (\ x → g x) =η g





transp : ∀ {l} (A : I → Set l) → A i0 → A i1
transp A a = primComp A i0 (\ _ → empty) a




pathJ : ∀ {a}{b}{A : Set a}{x : A}(P : ∀ y → Path x y → Set b)
        → P x refl →
        ∀ y (p : Path x y) → P y p
pathJ P d _ p =  transp (λ i → P (p i) (\ j → p (i ∧ j))) d






-- primComp : ∀ {a} (A : (i : I) → Set (a i)) (φ : I)
--            → (u : ∀ i → Partial (A i) φ) → (a : A i0) → A i1

-- ("Partial φ A" is something like "(φ = i1) → A")


{-
Example:  i : 𝕀 ⊢ primComp A (i ∨ ~ i) u a

          ^
        j |
          --->
           i



                   primComp A (i ∨ ~ i) u a
   (u 1)(i = 0) -----------------------------> (u 1)(i = 1)
                ^                            |
                |                            |
                |                            |
                |                            |
   (u j)(i = 0) |                            | (u j)(i = 1)
                |                            |
                |                            |
                |                            |
              a -----------------------------> a
                               a



-}




{-


 primComp (\ _ -> A) i1 (\ j _ → p j) x
               ^
               |
               | p j
               |
               x

-}

test-primComp : ∀ {a} (A : Set a) {x y : A} (p : Path x y)
                → primComp (\ _ → A) i1 (\ j _ → p j) x ≡ y
test-primComp A p = refl







transp-coh : ∀ {l} → (A : I → Set l) → (x : A i0) → PathP A x (transp A x)
transp-coh A x i = primComp (\ j → A (i ∧ j)) (~ i) (\ { j (i = i0) → x }) x





pathJprop : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Path x y → Set p)
            → (d : P x refl)
            → pathJ P d _ refl ≡ d
pathJprop {x = x} P d = sym (transp-coh (λ i → P x refl) d)








-- conid : {a : Level} {A : Set a} {x y : A} → (φ : I) → Path x y → Id x y

reflId : ∀ {a} {A : Set a}{x : A} → Id x x
reflId {x = x} = conid i1 (λ _ → x)

Jdef : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Id x y → Set p) → (d : P x reflId)
       → J P d reflId ≡ d
Jdef P d = refl

fromPath : ∀ {A : Set}{x y : A} → Path x y -> Id x y
fromPath p = conid i0 (\ i → p i)
