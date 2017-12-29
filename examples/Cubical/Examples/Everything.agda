module Cubical.Examples.Everything where


-- Circle as HIT, postulating the constructors and providing
-- computation with REWRITE
open import Cubical.Examples.Circle

-- We can prove bisimilar streams equal by copatterns, where Stream is
-- the "standard" coinductive record definition.
open import Cubical.Examples.Stream

-- Testing
open import Cubical.Examples.Cube
open import Cubical.Examples.OTTU

open import Cubical.Examples.BinNat
open import Cubical.Examples.Int
open import Cubical.Examples.SizedStream

open import Cubical.Examples.Category
open import Cubical.Examples.FunctorCWF


-- Demo
open import Cubical.Examples.AIM_Demo.DemoPath
open import Cubical.Examples.AIM_Demo.DemoPartial
open import Cubical.Examples.AIM_Demo.DemoGlue
open import Cubical.Examples.AIM_Demo.DemoUniv
