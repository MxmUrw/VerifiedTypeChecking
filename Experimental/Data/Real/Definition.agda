
module Verification.Experimental.Data.Real.Definition where

open import Verification.Conventions
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder

-- mostly from https://ncatlab.org/nlab/show/real+number



record Cut (L U : 𝒫 ℚ) : 𝒰₀ where
  field elA : ∑ λ a -> L a
  field elB : ∑ λ b -> U b
  field downclosed-L : ∀{a b : ℚ} -> a < b -> L b -> L a


-- ℝ : 𝒰₁
-- ℝ = ∑ λ A -> ∑ λ B -> Cut A B


