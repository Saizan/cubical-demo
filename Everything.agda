module Everything where

-- Basic primitives (some are from Agda.Primitive)
open import Primitives

-- Some library functions like refl/sym/trans plus Glue and composition for it.
open import PathPrelude

-- Lemmas on Sigma types
open import Sigma

-- Isomorphic types are equivalent
open import GradLemma

-- Equivalent types are equal, using Glue and GradLemma
open import Univalence

-- A[φ ↦ u] as a non-fibrant type
open import Sub

-- Id type where J computes definitionally, eliminator's type defined with Sub
open import Id

-- Circle as HIT, postulating the constructors and providing
-- computation with REWRITE
open import Circle

-- We can prove bisimilar streams equal by copatterns, where Stream is
-- the "standard" coinductive record definition.
open import Stream

-- Testing
open import Cube
open import OTTU

open import binnat

-- Demo
open import AIM_Demo.DemoPath
open import AIM_Demo.DemoPartial
open import AIM_Demo.DemoGlue
open import AIM_Demo.DemoUniv
