
module Verification.Experimental.Algebra.Monoid.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid.Definition

record isMonoid (A : Setoid 𝑗) : 𝒰 (𝑗) where
  field _⋆_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        ◌ : ⟨ A ⟩
        unit-l-⋆ : ∀{a} -> ◌ ⋆ a ∼ a
        unit-r-⋆ : ∀{a} -> a ⋆ ◌ ∼ a
        assoc-l-⋆ : ∀{a b c} -> (a ⋆ b) ⋆ c ∼ a ⋆ (b ⋆ c)
        assoc-r-⋆ : ∀{a b c} -> a ⋆ (b ⋆ c) ∼ (a ⋆ b) ⋆ c
        _`cong-⋆`_ : ∀{a₀ a₁ b₀ b₁} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋆ b₀ ∼ a₁ ⋆ b₁
  _≀⋆≀_ = _`cong-⋆`_
  infixl 50 _⋆_ _`cong-⋆`_ _≀⋆≀_
open isMonoid {{...}} public

Monoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Monoid 𝑗 = Setoid 𝑗 :& isMonoid

record isCommutative (A : Monoid 𝑗) : 𝒰 𝑗 where
  field comm-⋆ : ∀{a b : ⟨ A ⟩} -> a ⋆ b ∼ b ⋆ a

open isCommutative {{...}} public


record isSubmonoid {A} {{_ : Monoid 𝑗 on A}} (P : 𝒫 A :& isSubsetoid) : 𝒰 𝑗 where
  field closed-◌ : ⟨ P ⟩ ◌
        closed-⋆ : ∀{a b} -> ⟨ P ⟩ a -> ⟨ P ⟩ b -> ⟨ P ⟩ (a ⋆ b)
open isSubmonoid {{...}} public






