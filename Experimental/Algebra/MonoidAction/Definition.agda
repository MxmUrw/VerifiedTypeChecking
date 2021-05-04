
module Verification.Experimental.Algebra.MonoidAction.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Algebra.Monoid.Definition


record hasAction-l (M : Monoid 𝑖) (A : Setoid 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field _↷_ : ⟨ M ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        assoc-l-↷ : ∀{m n a} -> (m ⋆ n) ↷ a ∼ m ↷ (n ↷ a)

  infixr 30 _↷_
open hasAction-l {{...}} public


