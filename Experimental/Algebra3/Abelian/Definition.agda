
{-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra.Abelian.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
open import Verification.Experimental.Algebra.Group.Quotient


Abelian : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Abelian 𝑗 = Monoid 𝑗 :& (isGroup :, isCommutative)

Subabelian : (A : Abelian 𝑗) -> 𝒰 _
Subabelian A = Subgroup ′ ⟨ A ⟩ ′


-- module _ {A : Abelian 𝑗} where
--   RelSubabelian : Subabelian A -> ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 _
--   RelSubabelian B = RelSubgroup ′ ⟨ B ⟩ ′

-- RelSubabelian : {A : Abelian 𝑗} (B : Subabelian A) -> 

module _ {A : Abelian 𝑗} {B : Subabelian A} where
  private
    instance
      isNormal:Subabelian : isNormal ′ ⟨ B ⟩ ′
      isNormal.normal isNormal:Subabelian a {b} b∈B =
        let P₀ = b             ≣⟨ unit-r-⋆ ⁻¹ ⟩
                 b ⋆ ◌         ≣⟨ refl `cong-⋆` inv-r-⋆ ⁻¹ ⟩
                 b ⋆ (a ⋆ ◡ a) ≣⟨ assoc-r-⋆ ⟩
                 b ⋆ a ⋆ ◡ a   ≣⟨ comm-⋆ `cong-⋆` refl ⟩
                 a ⋆ b ⋆ ◡ a   ∎

            P₁ : ⟨ B ⟩ (a ⋆ b ⋆ ◡ a)
            P₁ = transp-Subsetoid P₀ b∈B
        in P₁

  -- testaa : (a b : ⟨ ′ ⟨ A ⟩ ′ /-Group B ⟩) -> 𝟙-𝒰
  -- testaa a b =
  --   let x = a ⋆ b
  --   in {!!}

  -- instance
  --   open _:&_ (′ ⟨ A ⟩ ′ /-Group B)

  -- instance
  --   -- isCommutative:AbelianQuot : isCommutative ′ ⟨  ⟩ ′
  --   isCommutative:AbelianQuot : isCommutative (′ ⟨ ′ ⟨ A ⟩ ′ /-Group B ⟩ ′)
  --   isCommutative:AbelianQuot = ?
  --   isCommutative.comm-⋆ isCommutative:AbelianQuot {a = [ a ]} {b = [ b ]} = preserves-∼ comm-⋆

-- _/-Abelian_ : (A : Abelian 𝑗) -> (B : Subabelian A) -> Abelian _
-- _/-Abelian_ A B = ′ ⟨ A ⟩ ′ /-Group B


