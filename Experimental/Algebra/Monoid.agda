
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra.Monoid where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure

record isSetoid (𝑗 : 𝔏) (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field _∼_ : A -> A -> 𝒰 𝑗
        {{isEquivRel:∼}} : isEquivRel _∼_
open isSetoid {{...}} public

Setoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Setoid 𝑗 = 𝒰 (𝑗 ⌄ 0) :& isSetoid (𝑗 ⌄ 1)

record isSetoidHom (A : Setoid 𝑖) (B : Setoid 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  field map-∼ : ∀{a b} -> a ∼ b -> f a ∼ f b
open isSetoidHom {{...}} public
-- instance
--   isCategory:Setoid


record isMonoid (A : Setoid 𝑗) : 𝒰 (𝑗) where
  field _⋆_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        ◌ : ⟨ A ⟩
        unit-l-⋆ : ∀{a} -> ◌ ⋆ a ∼ a
        unit-r-⋆ : ∀{a} -> a ⋆ ◌ ∼ a
        assoc-l-⋆ : ∀{a b c} -> (a ⋆ b) ⋆ c ∼ a ⋆ (b ⋆ c)
        assoc-r-⋆ : ∀{a b c} -> a ⋆ (b ⋆ c) ∼ (a ⋆ b) ⋆ c
        _`cong-⋆`_ : ∀{a₀ a₁ b₀ b₁} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋆ b₀ ∼ a₁ ⋆ b₁
  infixl 50 _⋆_ _`cong-⋆`_
open isMonoid {{...}} public

Monoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Monoid 𝑗 = Setoid 𝑗 :& isMonoid

record isCommutative (A : Setoid 𝑗 :& isMonoid) : 𝒰 𝑗 where
  field comm-⋆ : ∀{a b : ⟨ A ⟩} -> a ⋆ b ∼ b ⋆ a

open isCommutative {{...}} public

record isGroup (A : Monoid 𝑗) : 𝒰 𝑗 where
  field ◡_ : ⟨ A ⟩ -> ⟨ A ⟩
        inv-l-⋆ : ∀{a} -> ◡ a ⋆ a ∼ ◌
        inv-r-⋆ : ∀{a} -> a ⋆ ◡ a ∼ ◌
        cong-◡_ : ∀{a₀ a₁} -> a₀ ∼ a₁ -> ◡ a₀ ∼ ◡ a₁
  infix 100 ◡_
open isGroup {{...}} public

Group : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Group 𝑗 = Monoid 𝑗 :& isGroup

module _ {A : 𝒰 𝑖} {{_ : Group (𝑖 , 𝑗) on A}} where
  cancel-l-⋆ : ∀{a b c : A} -> a ⋆ b ∼ a ⋆ c -> b ∼ c
  cancel-l-⋆ {a} {b} {c} p =
      b             ≣⟨ unit-l-⋆ ⁻¹ ⟩
      ◌ ⋆ b         ≣⟨ inv-l-⋆ ⁻¹ `cong-⋆` refl ⟩
      (◡ a ⋆ a) ⋆ b ≣⟨ assoc-l-⋆ ⟩
      ◡ a ⋆ (a ⋆ b) ≣⟨ refl `cong-⋆` p ⟩
      ◡ a ⋆ (a ⋆ c) ≣⟨ assoc-r-⋆ ⟩
      (◡ a ⋆ a) ⋆ c ≣⟨ inv-l-⋆ `cong-⋆` refl ⟩
      ◌ ⋆ c         ≣⟨ unit-l-⋆ ⟩
      c             ∎

  distr-⋆-◡ : ∀{a b : A} -> ◡ (a ⋆ b) ∼ ◡ b ⋆ ◡ a
  distr-⋆-◡ {a} {b} = cancel-l-⋆ $
    (a ⋆ b) ⋆ ◡ (a ⋆ b)   ≣⟨ inv-r-⋆ ⟩
    ◌                     ≣⟨ inv-r-⋆ ⁻¹ ⟩
    a ⋆ ◡ a               ≣⟨ unit-r-⋆ ⁻¹ `cong-⋆` refl ⟩
    (a ⋆ ◌) ⋆ ◡ a         ≣⟨ (refl `cong-⋆` inv-r-⋆ ⁻¹) `cong-⋆` refl ⟩
    (a ⋆ (b ⋆ ◡ b)) ⋆ ◡ a ≣⟨ assoc-r-⋆ `cong-⋆` refl ⟩
    ((a ⋆ b) ⋆ ◡ b) ⋆ ◡ a ≣⟨ assoc-l-⋆ ⟩
    (a ⋆ b) ⋆ (◡ b ⋆ ◡ a) ∎

  double-◡ : ∀{a : A} -> ◡ ◡ a ∼ a
  double-◡ {a} = cancel-l-⋆ $
    ◡ a ⋆ ◡ ◡ a ≣⟨ inv-r-⋆ ⟩
    ◌           ≣⟨ inv-l-⋆ ⁻¹ ⟩
    ◡ a ⋆ a     ∎



-- record isRing (A : Monoid 𝑗 :& isCommutative :& isSemiring :, (λ A -> isGroup (make& (⟨ A ⟩)))) : 𝒰 𝑗 where

-- record asMultiplicative (A : Monoid 𝑗) : 𝒰 𝑗 where

-- record doubleMon (A : Setoid 𝑗 :& (λ A -> (A :& isMonoid :& asMultiplicative) A) :, isMonoid) : 𝒰 𝑗 where
--   field testasdf : ∀{a b : ⟨ A ⟩} -> a ⋆ b ∼ a
