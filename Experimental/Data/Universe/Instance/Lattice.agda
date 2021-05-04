
module Verification.Experimental.Data.Universe.Instance.Lattice where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Instance.Setoid
open import Verification.Experimental.Data.Universe.Instance.Preorder

instance
  hasFiniteJoins:𝒰 : hasFiniteJoins ′ 𝒰 𝑖 ′
  hasFiniteJoins.⊥         hasFiniteJoins:𝒰 = ⊥-𝒰
  hasFiniteJoins.initial-⊥ hasFiniteJoins:𝒰 = incl $ λ {()}
  hasFiniteJoins._∨_       hasFiniteJoins:𝒰 = _+-𝒰_
  hasFiniteJoins.ι₀-∨      hasFiniteJoins:𝒰 = incl left
  hasFiniteJoins.ι₁-∨      hasFiniteJoins:𝒰 = incl right
  hasFiniteJoins.[_,_]-∨   hasFiniteJoins:𝒰 f g = incl $ either ⟨ f ⟩ ⟨ g ⟩


