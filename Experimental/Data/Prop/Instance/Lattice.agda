
module Verification.Experimental.Data.Prop.Instance.Lattice where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Data.Prop.Instance.Setoid
open import Verification.Experimental.Data.Prop.Instance.Preorder
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Instance.Preorder
open import Verification.Experimental.Data.Universe.Instance.Lattice
open import Verification.Experimental.Data.Sum.Definition

-- data ⊥-Prop {𝑖} : Prop 𝑖 where

instance
  hasFiniteJoins:Prop : hasFiniteJoins ′ Prop 𝑖 ′
  hasFiniteJoins.⊥         hasFiniteJoins:Prop = ∣ ⊥-𝒰 ∣
  hasFiniteJoins.initial-⊥ hasFiniteJoins:Prop = incl $ λ {()}
  hasFiniteJoins._∨_       hasFiniteJoins:Prop = λ A B -> ∣ ⟨ A ⟩ +-𝒰 ⟨ B ⟩ ∣
  hasFiniteJoins.ι₀-∨      hasFiniteJoins:Prop = incl left
  hasFiniteJoins.ι₁-∨      hasFiniteJoins:Prop = incl right
  hasFiniteJoins.[_,_]-∨   hasFiniteJoins:Prop f g = incl $ either ⟨ f ⟩ ⟨ g ⟩

