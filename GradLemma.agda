{-# OPTIONS --cubical #-}
module GradLemma where

open import PathPrelude

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

module _ {l l' : _}  where
  private
    U = Set l
    V = Set l'

  fiber : {A : U}{B : V} → (f : A → B) → (b : B) → _
  fiber f b = Σ _ \ a → b ≡ f a

  Square : ∀ {a} {A : Set a} {a0 a1 b0 b1 : A}
                 (u : Path a0 a1) (v : Path b0 b1)
                                (r0 : Path a0 b0) (r1 : Path a1 b1) → Set a
  Square {A = A} u v r0 r1 = PathP (\ i → (Path (u i) (v i))) r0 r1

  lemIso : {A : U} {B : V} (f : A -> B) (g : B -> A)
         (s : (y : B) -> (f (g y)) ≡ y)
         (t : (x : A) -> (g (f x)) ≡ x)
         (y : B) (x0 x1 : A) (p0 : y ≡ (f x0)) (p1 : y ≡ (f x1))
         → Path {A = fiber f y} (x0 , p0) (x1 , p1)
  lemIso {A} {B} f g s t y x0 x1 p0 p1 = \ i → (p i) , sq1 i
   where
     rem0 : g y ≡ x0
     rem0 = \ i → primComp (\ _ → A) _ (\ k → \ { (i = i1) → t x0 k; (i = i0) → g y }) (g (p0 i))
     rem1 : g y ≡ x1
     rem1 = \ i → primComp (\ _ → A) (i ∨ ~ i) (\ k → \ {(i = i1) → t x1 k; (i = i0) → g y})  (g (p1 i))
     p : Path x0 x1
     p = \ i → primComp (\ _ → A) (i ∨ ~ i) (\ k → \{ (i = i1) → rem1 k; (i = i0) → rem0 k })  (g y)
     fill0 : Square
                       (\ i → g (p0 i)) rem0 (\ i → g y) (t x0)
     fill0 = \ i → \ j → primComp (λ _ → A) _                 (\ k → \ { (i = i1) → t x0 (j ∧ k)
                                                                       ; (i = i0) → g y
                                                                       ; (j = i0) → g (p0 i) })
                                            (g (p0 i))
     fill1 : Square
                       (\ i → g (p1 i)) rem1 (\ i → g y) (t x1)
     fill1 = \ i → \ j → primComp (λ _ → A) (i ∨ (~ i ∨ ~ j)) (\ k → \ { (i = i1) → t x1 (j ∧ k)
                                                                       ; (i = i0) → g y
                                                                       ; (j = i0) → g (p1 i) })
                                            (g (p1 i))

     fill2 : Square {A = A} (\ k → g y) p rem0 rem1
     fill2 = \ i → \ j → primComp (λ _ → A) (i ∨ (~ i ∨ ~ j)) (\ k → \ { (i = i1) → rem1 (j ∧ k)
                                                                       ; (i = i0) → rem0 (j ∧ k)
                                                                       ; (j = i0) → g y })
                                            (g y)

     sq : Square {A = A} (\ _ → g y) (\ i → g (f (p i))) (\ j → g (p0 j)) (\ j → g (p1 j))
     sq = \ i → \ j → primComp (\ _ → A) ((i ∨ (~ i)) ∨ (j ∨ (~ j))) (\ k → \ { (i = i1) → fill1 j (~ k)
                                                                              ; (i = i0) → fill0 j (~ k)
                                                                              ; (j = i1) → t (p i) (~ k)
                                                                              ; (j = i0) → g y           })
                               (fill2 i j)
     sq1 : Square {A = B} (\ _ → y) (\ i → f (p i)) p0 p1
     sq1 = \ i → \ j → primComp (\ _ → B) ((i ∨ (~ i)) ∨ (j ∨ (~ j))) (\ k → \ { (i = i1) → s (p1 j) k
                                                                               ; (i = i0) → s (p0 j) k
                                                                               ; (j = i1) → s (f (p i)) k
                                                                               ; (j = i0) → s y k })
                                (f (sq i j))


  gradLemma : {A : U} {B : V} (f : A -> B) (g : B -> A)
         (s : (y : B) -> Path (f (g y)) y)
         (t : (x : A) -> Path (g (f x)) x) → Equiv.isEquiv A B f
  gradLemma f g s t = \ y -> (g y , \ i →  s y (~ i)) , \ z ->
      lemIso f g s t y (g y) (fst z) (\ i → s y (~ i)) (snd z)


  invEq : {A : U} {B : V} (w : Equiv.Equiv A B) (y : B) → A
  invEq w y = fst (fst (snd w y))

  secEq : {A : U} {B : V} (w : Equiv.Equiv A B) (x : A) → Path (invEq w (fst w x)) x
  secEq w x = \ i → fst (snd (snd w (fst w x)) (x , (\ j → fst w x)) i)

  retEq : {A : U} {B : V} (w : Equiv.Equiv A B) (y : B) → Path (fst w (invEq w y)) y
  retEq w y = \ i → snd (fst (snd w y)) (~ i)

prop : ∀ {a} → (A : Set a) → Set a
prop A = (a b : A) -> Path a b

lemProp : ∀ {a} {A : Set a} (h : A -> prop A) → prop A
lemProp h = \ a  -> h a a

module _ {l l' : _}  where
  private
    U = Set l
    V = Set l'

  invEquiv : {A : U} {B : V} (f : Equiv.Equiv A B) → Equiv.Equiv B A
  invEquiv {A} {B} f = invEq f , gradLemma (invEq f) (fst f) (secEq f) (retEq f)


  propPi : {A : U} {B : A -> V} (h : (x : A) -> prop (B x))
         (f0 f1 : (x : A) -> B x) → Path f0 f1
  propPi h f0 f1  = \ i → \ x -> (h x (f0 x) (f1 x)) i


  lemPropF : {A : U} {P : A -> V} (pP : (x : A) -> prop (P x)) {a0 a1 : A}
           (p : Path a0 a1) {b0 : P a0} {b1 : P a1} → PathP (\ i → P (p i)) b0 b1
  lemPropF {P = P} pP p {b0} {b1} = \ i → pP (p i) (primComp (\ j → P (p (i ∧ j)) ) (~ i) (\ _ →  \ { _ → b0 }) b0)
                                                     ((primComp (\ j → P (p (i ∨ ~ j)) ) (i) (\ _ → \{ _ → b1 }) b1)) i

  lemSig : {A : U} {B : A -> V} (pB : (x : A) -> prop (B x))
         (u v : Σ A B) (p : Path (fst u) (fst v))
         → Path u v
  lemSig {B = B} pB u v p = \ i → (p i) , ((lemPropF {P = B} pB p) {snd u} {snd v} i)

  propSig : {A : U} {B : A -> V} (pA : prop A) (pB : (x : A) -> prop (B x))
            → prop (Σ A B)
  propSig {A} {B} pA pB t u = lemSig pB t u (pA (fst t) (fst u))


module _ {l : _}  where
  private
    U = Set l

  set : U → U
  set A = (a b : A) → prop (Path a b)

  propSet : {A : U} (h : prop A) → set A
  propSet {A} h =
   \(a b : A) (p q : Path a b) ->
     \ j → \ i → primComp (\ k → A)
                          ((~ i ∨ i) ∨ (~ j ∨ j))
                          (\ k → \ { (i = i0) → h a a k; (i = i1) → h a b k
                                   ; (j = i0) → h a (p i) k; (j = i1) → h a (q i) k })
                          a

  propIsContr : {A : U} → prop (Contr.isContr A)
  propIsContr {A} = lemProp (\ t → propSig (λ a b → trans (sym (snd t a)) (snd t b))
                            (λ x → propPi (propSet ((λ a b → trans (sym (snd t a)) (snd t b))) x)))

module _ {l l' : _}  where
  private
    U = Set l
    V = Set l'

  propIsEquiv : {A : U} {B : V} (f : A -> B) → prop (Equiv.isEquiv A B f)
  propIsEquiv f = \ u0 u1 -> \ i → \ y -> propIsContr (u0 y) (u1 y) i

  invEquiv-invol : {A : U} {B : V} (f : Equiv.Equiv A B) → Path (invEquiv (invEquiv f)) f
  invEquiv-invol f = \ i → fst f , (propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i)
