{-# OPTIONS --cubical #-}
module Cubical.Examples.FunctorCWF where

open import Cubical.PathPrelude
open import Cubical.Prelude hiding (_∘_)

Σ= : ∀ {a b} {A : Set a} {B : A → Set b} {x y : Σ A B} (eq : x .fst ≡ y .fst)
     → PathP (\ i → B (eq i)) (x .snd) (y .snd) → x ≡ y
Σ= eq p i .fst = eq i
Σ= eq p i .snd = p i


-- We define category the naive way, without requiring the Hom-types to
-- be truncated.
record Category {o h} : Set (ℓ-suc (ℓ-max o h)) where
  no-eta-equality
  constructor con
  field
    Obj : Set o
    Hom : Obj → Obj → Set h

  _⇒_ = Hom
  field
    id : ∀ {X : Obj} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    id-left : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    id-right : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D} (f : Hom C D) (g : Hom B C) (h : Hom A B)
              → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h

open Category


-- We call 1-cat a category whose Hom-types are h-sets
1-cat : ∀ {o1 h1} (C : Category {o1} {h1}) → Set _
1-cat C = ∀ X Y → isSet (Hom C X Y)


-- Functor
record Functor {o1 h1 o2 h2} (C : Category {o1} {h1})(D : Category {o2} {h2})
               : Set (ℓ-suc (ℓ-max (ℓ-max o1 h1) (ℓ-max o2 h2))) where
  no-eta-equality
  constructor con
  private
    module C = Category C
    module D = Category D
  field
    obj      : C .Obj → D .Obj
    hom      : {A B : C .Obj} → (A C.⇒ B) → (obj A) D.⇒ (obj B)
    presId   : {A : C .Obj} → hom (C .id {A}) ≡ D .id {obj A}
    presComp : {A B C : C .Obj} → (f : A C.⇒ B) → (g : B C.⇒ C) →
                 hom (g C.∘ f) ≡ (hom g) D.∘ (hom f)


open Functor

-- Composition of Functors
infixr 45 _∘ᶠ_

_∘ᶠ_ : ∀ {oa ha ob hb oc hc}
       {A : Category {oa} {ha}} {B : Category {ob} {hb}} {C : Category {oc} {hc}}
       → Functor B C → Functor A B → Functor A C
(G ∘ᶠ F) .obj a = G .obj (F .obj a)
(G ∘ᶠ F) .hom f = G .hom (F .hom f)
(G ∘ᶠ F) .presId       = trans (cong (G .hom) (F .presId)) (G .presId)
(G ∘ᶠ F) .presComp f g = trans (cong (G .hom) (F .presComp f g))
                               (G .presComp (F .hom f) (F .hom g))



-- Functors into a 1-cat are equal iff their actions on objects and arrows are equal.

Func≡ : ∀ {o1 h1 o2 h2} {C : Category {o1} {h1}} {D : Category {o2} {h2}}
        → 1-cat D → {F G : Functor C D}
        → (eq : F .obj ≡ G .obj)
        → PathP (\ i → ∀ (X Y : C .Obj) → Hom C X Y → Hom D (eq i X) (eq i Y))
                (\ _ _ → F .hom) (\ _ _ → G .hom)
        → F ≡ G
Func≡ {C = C} {D} 1-D {F} {G} eq p = r where
  mutual
   H : (X : _) → PathP (λ z → PathP (λ _ → Hom D (eq z X) (eq z X))
                                    (p z _ _ (C .id)) (D .id))
                       (F .presId {X}) (G .presId {X})
   H X = toPathP (1-D _ _ _ _ _ _)
   H2 : ∀ {A B C1} → (f : Hom C A B) (g : Hom C B C1)
        → PathP (\ i → p i _ _ (C ._∘_ g f) ≡ (D ∘ p i _ _ g) (p i _ _ f))
                (F .presComp f g) (G .presComp f g)
   H2 {A} {B} {C} f g = toPathP (1-D _ _ _ _ _ _)
   r : F ≡ G
   r i .obj = eq i
   r i .hom = p i _ _
   r i .presId {X}   = H X i
   r i .presComp f g = H2 f g i


record NaturalTransformation
       {o1 h1 o2 h2} {C : Category {o1} {h1}} {D : Category {o2} {h2}}
       (F G : Functor C D) : Set (ℓ-max h2 (ℓ-max h1 o1)) where
  constructor con
  private
    module D = Category D
  field
    apply : ∀ {X} → Hom D (F .obj X) (G .obj X)
    natural : ∀ {X Y} (f : Hom C X Y)
              → apply {Y} D.∘ F .hom f ≡ G .hom f D.∘ apply {X}

open NaturalTransformation


-- Natural transformations into a 1-cat are equal iff they are equal as families of maps.

NT= : ∀ {o1 h1 o2 h2} {C : Category {o1} {h1}} {D : Category {o2} {h2}}
       {F G : Functor C D} {f g : NaturalTransformation F G} →
       (eq : Path {A = ∀ {X} → Hom D (F .obj X) (G .obj X)} (f .apply) (g .apply))
       → 1-cat D → f ≡ g
NT= eq p i .apply = eq i
NT= {D = D} {F} {G} {a} {b} eq p i .natural {X} {Y} f
  = toPathP
      {A = λ j →
         PathP (λ _ → D .Hom (F .obj X) (G .obj Y))
               (D ._∘_ (eq j) (F .hom f)) (D ._∘_ (G .hom f) (eq j))}
      {x = a .natural f} {y = b .natural f}
      (p _ _ _ _ _ _) i


-- Functor category, of functors F : C -> D into a 1-cat D
Func : ∀ {o1 h1 o2 h2} (C : Category {o1} {h1}) (D : Category {o2} {h2})
       → 1-cat D → Category
Func C D 1-D .Obj                  = Functor C D
Func C D 1-D .Hom                  = NaturalTransformation
Func C D 1-D .id {F} .apply        = D .id
Func C D 1-D .id .natural f        = trans (D .id-left _) (sym (D .id-right _))
(Func C D 1-D ._∘_ f g) .apply     = D ._∘_ (f .apply) (g .apply)
(Func C D 1-D ._∘_ f g) .natural h
      = trans (sym (D .∘-assoc _ _ _))
        (trans (cong (D ._∘_ (f .apply)) (g .natural h))
        (trans (D .∘-assoc _ _ _)
        (trans (cong (\ x → D ._∘_ x (g .apply)) (f .natural h))
               (sym (D .∘-assoc _ _ _)))))
Func C D 1-D .id-left  f           = NT= (\ i → D .id-left (f .apply) i) 1-D
Func C D 1-D .id-right f           = NT= (\ i →  D .id-right (f .apply) i) 1-D
Func C D 1-D .∘-assoc f g h
  = NT= (\ i → D .∘-assoc (f .apply) (g .apply) (h .apply) i) 1-D



hSets : (o : Level) → Category
hSets o .Obj                 = Σ (Set o) isSet
hSets o .Hom (A , _) (B , _) = A → B
hSets o .id                  = \ x → x
hSets o ._∘_ f g x           = f (g x)
hSets o .id-left f           = refl
hSets o .id-right f          = refl
hSets o .∘-assoc f g h       = refl

1-Sets : ∀ o → 1-cat (hSets o)
1-Sets o (X , Xset) (Y , Yset) f g p q
  = \ i → funExt (\ x → Yset (f x) (g x) (\ j → p j x) (\ j → q j x) i)



module Model (C : Category {ℓ-zero} {ℓ-zero}) where
  module C = Category C

  Cxt = Func C (hSets ℓ-zero) (1-Sets ℓ-zero)

  is-h-set : ∀ (G : Cxt .Obj) → (c : C .Obj) → isSet (G .obj c .fst)
  is-h-set G c = G .obj c .snd

  Elem : Cxt .Obj → Category
  Elem G .Obj                    = Σ (C .Obj) (\ c → G .obj c .fst)
  Elem G .Hom (c , gc)  (d , gd) = Σ (C .Hom c d) \ f → G .hom f gc ≡ gd
  Elem G .id     .fst            = C .id
  Elem G .id {X} .snd i          = G .presId i (X .snd)
  Elem G ._∘_     f g .fst       = f .fst C.∘ g .fst
  Elem G ._∘_ {X} f g .snd
    = trans (\ i → G .presComp (g .fst) (f .fst) i (X .snd))
     (trans (cong (G .hom (f .fst)) (g .snd)) (f .snd))
  Elem G .id-left  {X} {Y} f
    = Σ= (C .id-left (f .fst))  (toPathP (is-h-set G (Y .fst) _ _ _ _))
  Elem G .id-right {X} {Y} f
    = Σ= (C .id-right (f .fst)) (toPathP (is-h-set G (Y .fst) _ _ _ _))
  Elem G .∘-assoc {D = D} f g h
    = Σ= (C.∘-assoc _ _ _)      (toPathP (is-h-set G (D .fst) _ _ _ _ ))

  substElem : ∀ {Γ Δ : Functor C (hSets ℓ-zero)}
         {A B : Elem Γ .Obj}
         (σ : NaturalTransformation Γ Δ)
         (f : Elem Γ .Hom A B) →
          PathP (λ _ → Δ .obj (B .fst) .fst)
            (Δ .hom (f .fst) (σ .apply (A .snd))) (σ .apply (B .snd))
  substElem σ f = trans (sym (let H = _ in \ i → σ .natural (f .fst) i H))
                        (cong (σ .apply) (f .snd))

  ElemHom : ∀ {Γ Δ} → Cxt .Hom Γ Δ → Functor (Elem Γ) (Elem Δ)
  ElemHom {Γ} {Δ} σ .obj (c , g)  = c , σ .apply g
  ElemHom {Γ} {Δ} σ .hom f        = f .fst , substElem σ f
  ElemHom {Γ} {Δ} σ .presId       = Σ= refl (toPathP (is-h-set Δ _ _ _ _ _))
  ElemHom {Γ} {Δ} σ .presComp f g = Σ= refl (toPathP (is-h-set Δ _ _ _ _ _))


  Subst = Cxt .Hom

  Ty : Cxt .Obj → Set _
  Ty G = Functor (Elem G) (hSets ℓ-zero)

  subTy : ∀ {Γ Δ : Cxt .Obj} → Ty Δ → Subst Γ Δ → Ty Γ
  subTy A σ = A ∘ᶠ ElemHom σ

  -- Tm G A as a Limit of A.
  record Tm (G : Cxt .Obj) (A : Ty G) : Set where
    no-eta-equality
    constructor con
    field
      tm : ∀ ρ → A .obj ρ .fst
      tm-nat : ∀ {ρ1 ρ2}
               (f : Hom (Elem G) ρ1 ρ2)
               → A .hom f (tm ρ1) ≡ tm ρ2
  open Tm

  subTm : ∀ {Γ Δ : Cxt .Obj} → {A : Ty Δ}
          → (t : Tm Δ A) → (σ : Subst Γ Δ) → Tm Γ (subTy A σ)
  subTm t σ .tm ρ           = t .tm (ElemHom σ .obj ρ)
  subTm t σ .tm-nat f = t .tm-nat (ElemHom σ .hom f)

  subTy-id : ∀ {G : Cxt .Obj} → (A : Ty G) → subTy A (Cxt .id {G}) ≡ A
  subTy-id {G} A
    = Func≡ (1-Sets ℓ-zero)
            refl
            \ i X Y f a →
              A .hom (f .fst , is-h-set G (Y .fst) _ _
                                         (substElem (Cxt .id {G}) f)
                                         (f .snd) i)
                     a

  subTm-id : ∀ {G : Cxt .Obj} (A : Ty G) (t : Tm G A)
             → PathP (\ i → Tm G (subTy-id A i)) (subTm t (Cxt .id {G})) t
  subTm-id {G} A t i .tm ρ = t .tm ρ
  subTm-id {G} A t i .tm-nat {c1 , γ1} {c2 , γ2} f
           = t .tm-nat
                       (f .fst ,
                         is-h-set G c2
                                  (G .hom (f .fst) (Cxt .id {G} .apply γ1))
                                  (Cxt .id {G} .apply γ2)
                                  (substElem (Cxt .id {G}) f)
                                  (f .snd)
                                  i)


--   (A : ∀ G → Ty G), (σ : Subst D G) → subTy σ (A G) .obj = A D .obj
--        → subTy σ (A G) ≡ A D ?
