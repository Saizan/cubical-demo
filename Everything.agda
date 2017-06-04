module Everything where

-- Basic primitives (some are from Agda.Primitive)
open import Primitives

-- Some library functions like refl/sym/trans plus Glue and composition for it.
open import PathPrelude

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
