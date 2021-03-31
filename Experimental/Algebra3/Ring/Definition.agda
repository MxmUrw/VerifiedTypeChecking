
module Verification.Experimental.Algebra.Ring.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition


record isSemiring (A : Monoid 𝑗 :& isCommutative) : 𝒰 𝑗 where
  field _⋅_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        ⨡ : ⟨ A ⟩
        unit-l-⋅ : ∀{a} -> ⨡ ⋅ a ∼ a
        unit-r-⋅ : ∀{a} -> a ⋅ ⨡ ∼ a
        assoc-l-⋅ : ∀{a b c} -> (a ⋅ b) ⋅ c ∼ a ⋅ (b ⋅ c)
        distr-l-⋅ : ∀{a b c : ⟨ A ⟩} -> a ⋅ (b ⋆ c) ∼ a ⋅ b ⋆ a ⋅ c
        distr-r-⋅ : ∀{a b c : ⟨ A ⟩} -> (b ⋆ c) ⋅ a ∼ b ⋅ a ⋆ c ⋅ a
  infixl 80 _⋅_
open isSemiring {{...}} public

Semiring : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Semiring 𝑗 = (Monoid 𝑗 :& isCommutative) :& isSemiring


record isRing (A : Monoid 𝑗 :& (isCommutative :> isSemiring) :, isGroup) : 𝒰 𝑗 where

Ring : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Ring 𝑗 = (Monoid 𝑗 :& (isCommutative :> isSemiring) :, isGroup) :& isRing


--------------------------------------------------------------------------------
-- Ideals


record isIdeal {A} {{_ : Ring 𝑗 on A}} (P : 𝒫 A :& isSubsetoid :& isSubmonoid :& isSubgroup) : 𝒰 𝑗 where
  field ideal-l-⋅ : ∀{a b} -> ⟨ P ⟩ b -> ⟨ P ⟩ (a ⋅ b)
        ideal-r-⋅ : ∀{a b} -> ⟨ P ⟩ a -> ⟨ P ⟩ (a ⋅ b)
open isIdeal {{...}} public

Ideal : (R : Ring 𝑗) -> 𝒰 _
Ideal R = Subgroup ′ ⟨ R ⟩ ′ :& isIdeal

module _ {R : Ring 𝑗} where
  RelIdeal : Ideal R -> ⟨ R ⟩ -> ⟨ R ⟩ -> 𝒰 _
  RelIdeal I = RelSubgroup ′ ⟨ I ⟩ ′



record isPrime {R : Ring 𝑗} (I : Ideal R) : 𝒰 𝑗 where
  field prime : ∀{a b} -> ⟨ I ⟩ (a ⋅ b) -> ⟨ I ⟩ a +-𝒰 ⟨ I ⟩ b




