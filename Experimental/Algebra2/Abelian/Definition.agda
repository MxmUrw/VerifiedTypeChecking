
{-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra2.Abelian.Definition where


open import Verification.Conventions hiding (⟪_⟫ ; Structure ; ′_′)
open import Verification.Experimental.Meta.Structure5
open import Verification.Experimental.Algebra2.Typoid.Definition
open import Verification.Experimental.Algebra2.Monoid.Definition
open import Verification.Experimental.Algebra2.Group.Definition
open import Verification.Experimental.Algebra2.Group.Quotient


Abelian : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Abelian 𝑗 = Structure (is Monoid 𝑗 :> (isGroup :, isCommutative))

Subabelian : (A : Abelian 𝑗) -> 𝒰 _
Subabelian A = Subgroup ′ ⟨ A ⟩ ′


-- module _ {A : Abelian 𝑗} where
--   RelSubabelian : Subabelian A -> ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 _
--   RelSubabelian B = RelSubgroup ′ ⟨ B ⟩ ′

-- RelSubabelian : {A : Abelian 𝑗} (B : Subabelian A) -> 

module _ {A : Abelian 𝑗} {B : Subabelian A} where
  mytestinst : isGroup ⟨ A ⟩
  mytestinst = it
  {-
  private
    instance
      isNormal:Subabelian : isNormal ⟨ B ⟩
      isNormal.normal isNormal:Subabelian a {b} b∈B =
        let P₀ = b             ≣⟨ unit-r-⋆ ⁻¹ ⟩
                 b ⋆ ◌         ≣⟨ refl `cong-⋆` inv-r-⋆ ⁻¹ ⟩
                 b ⋆ (a ⋆ ◡ a) ≣⟨ assoc-r-⋆ ⟩
                 b ⋆ a ⋆ ◡ a   ≣⟨ comm-⋆ `cong-⋆` refl ⟩
                 a ⋆ b ⋆ ◡ a   ∎

            P₁ : ⟨ B ⟩ (a ⋆ b ⋆ ◡ a)
            P₁ = transp-Subtypoid P₀ b∈B
        in P₁
  -}

{-
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


-}
