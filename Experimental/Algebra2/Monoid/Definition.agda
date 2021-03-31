
module Verification.Experimental.Algebra2.Monoid.Definition where

-- open import Verification.Conventions
open import Verification.Conventions hiding (⟪_⟫ ; Structure ; ′_′)
open import Verification.Experimental.Meta.Structure5
open import Verification.Experimental.Algebra2.Typoid.Definition

-- record isMonoid A {{TT : Typoid 𝑗 on A}} : 𝒰 (𝑗) where
record isMonoid {𝑗 : 𝔏 ^ 2} A {{TT : (From (𝒰 (𝑗 ⌄ 0)) :> isTypoid (𝑗 ⌄ 1)) A}} : 𝒰 (𝑗) where
  field _⋆_ : A -> A -> A
        ◌ : A
        unit-l-⋆ : ∀{a} -> ◌ ⋆ a ∼ a
        unit-r-⋆ : ∀{a} -> a ⋆ ◌ ∼ a
        assoc-l-⋆ : ∀{a b c} -> (a ⋆ b) ⋆ c ∼ a ⋆ (b ⋆ c)
        assoc-r-⋆ : ∀{a b c} -> a ⋆ (b ⋆ c) ∼ (a ⋆ b) ⋆ c
        _`cong-⋆`_ : ∀{a₀ a₁ b₀ b₁} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋆ b₀ ∼ a₁ ⋆ b₁
  infixl 50 _⋆_ _`cong-⋆`_
open isMonoid {{...}} public

Monoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Monoid 𝑗 = Structure (is Typoid 𝑗 :> isMonoid)
-- Typoid 𝑗 :& isMonoid

record isCommutative A {{_ : Monoid 𝑗 on A}} : 𝒰 𝑗 where
  field comm-⋆ : ∀{a b : A} -> a ⋆ b ∼ b ⋆ a

open isCommutative {{...}} public


record isSubmonoid {A} {{_ : Monoid 𝑗 on A}} (P : 𝒫 A) {{_ : (From (𝒫 A) :> isSubtypoid) P}} : 𝒰 𝑗 where
  field closed-◌ : P ◌
        closed-⋆ : ∀{a b} -> P a -> P b -> P (a ⋆ b)
open isSubmonoid {{...}} public

Submonoid : Monoid 𝑗 -> 𝒰 _
Submonoid M = Structure (_ :> isSubmonoid {{of M}})

{-


-}



