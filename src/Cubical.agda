module Cubical where

-- Basic primitives (some are from Agda.Primitive)
open import Cubical.Primitives

-- Some library functions like refl/sym/trans plus Glue and composition for it.
open import Cubical.PathPrelude

-- Lemmas on Sigma types
open import Cubical.Sigma

-- Isomorphic types are equivalent
open import Cubical.GradLemma

-- Equivalent types are equal, using Glue and GradLemma
open import Cubical.Univalence

-- A[φ ↦ u] as a non-fibrant type
open import Cubical.Sub

-- Id type where J computes definitionally, eliminator's type defined with Sub
open import Cubical.Id

-- Circle as HIT, postulating the constructors and providing
-- computation with REWRITE
open import Cubical.Circle

-- We can prove bisimilar streams equal by copatterns, where Stream is
-- the "standard" coinductive record definition.
open import Cubical.Stream

-- Testing
open import Cubical.Cube
open import Cubical.OTTU

-- Demo
open import Cubical.AIM_Demo.DemoPath
open import Cubical.AIM_Demo.DemoPartial
open import Cubical.AIM_Demo.DemoGlue
open import Cubical.AIM_Demo.DemoUniv
