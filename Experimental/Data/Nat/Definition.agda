
module Verification.Experimental.Data.Nat.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Order.Preorder


instance
  isSetoid:ℕ : isSetoid _ ℕ
  isSetoid.myRel isSetoid:ℕ = _≡_
  isSetoid.isEquivRel:∼ isSetoid:ℕ = it


instance
  isPreorder:ℕ : isPreorder ′ ℕ ′
  isPreorder.myLE isPreorder:ℕ = _≤-ℕ_
  isPreorder.refl-≤ isPreorder:ℕ = incl refl-≤-ℕ
  isPreorder._∙-≤_ isPreorder:ℕ (incl p) (incl q) = incl (trans-≤-ℕ p q)
  isPreorder.transp-≤ isPreorder:ℕ (incl p) (incl q) (incl r) = incl (transport (λ i -> p i ≤-ℕ q i) r)

Preorder:ℕ : Preorder _
Preorder:ℕ = ′ ℕ ′


