
module Verification.Experimental.Algebra2.Group.Definition where

-- open import Verification.Conventions
open import Verification.Conventions hiding (⟪_⟫ ; Structure ; ′_′)
open import Verification.Experimental.Meta.Structure5
open import Verification.Experimental.Algebra2.Typoid.Definition
open import Verification.Experimental.Algebra2.Monoid.Definition


record isGroup A {{_ : Monoid 𝑗 on A}} : 𝒰 𝑗 where
  field ◡_ : A -> A
        inv-l-⋆ : ∀{a} -> ◡ a ⋆ a ∼ ◌
        inv-r-⋆ : ∀{a} -> a ⋆ ◡ a ∼ ◌
        cong-◡_ : ∀{a₀ a₁} -> a₀ ∼ a₁ -> ◡ a₀ ∼ ◡ a₁
  infix 100 ◡_
open isGroup {{...}} public

Group : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Group 𝑗 = Structure (is Monoid 𝑗 :> isGroup)
-- Monoid 𝑗 :& isGroup


record isSubgroup {A} {{_ : Group 𝑗 on A}}
       (P : 𝒫 A) {{_ : (_ :> isSubmonoid) P}}
       : 𝒰 𝑗 where
  field closed-◡ : ∀{a} -> P a -> P (◡ a)
open isSubgroup {{...}} public


Subgroup : (G : Group 𝑗) -> 𝒰 _
Subgroup G = Structure (_ :> isSubgroup {{of G}})
-- 𝒫 ⟨ G ⟩ :& isSubsetoid :& isSubmonoid :& isSubgroup


data RelSubgroup {G : Group 𝑗} (H : Subgroup G) (a : ⟨ G ⟩) (b : ⟨ G ⟩) : 𝒰 (𝑗 ⌄ 0) where
  incl : ⟨ H ⟩ (a ⋆ ◡ b) -> RelSubgroup H a b


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

{-
-}


