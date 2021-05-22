
module Verification.Experimental.Theory.Computation.Problem.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} (f : A -> B) where
  Img : (A -> 𝒰 𝑘) -> (B -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘))
  Img P b = ∑ λ a -> P a ×-𝒰 (f a ≣ b)

---------------------------------------------------------------
-- Definition of a problem

record isProblem (𝑖 : 𝔏) (A : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ⁺ ､ 𝑗 ⁺) where
  field 𝒱 : (A -> 𝒰 𝑗) -> 𝒰 (𝑗 ⊔ (𝑖 ⁺))

open isProblem {{...}} public

Problem : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
Problem 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isProblem (𝑖 ⌄ 1)


---------------------------------------------------------------
-- Definition of reductions

module _ (A : Problem (𝑖 , 𝑗)) (B : Problem (𝑖 , 𝑘)) where
  record isReduction (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
    field valid : ∀(P : ⟨ A ⟩ -> _) -> 𝒱 P -> 𝒱 (Img f P)

    -- field propMap : ∀(P : ⟨ A ⟩ -> _) -> Property P -> (Property (Img f P))
    -- field solutionMap : ∀(P : ⟨ A ⟩ -> _) -> (PX : Property P) -> ∀ a -> (pa : P a) -> (Solution (P , PX) a pa ↔ Solution (Img f P , propMap P PX) (f a) (a , (pa , refl)))

  Reduction : 𝒰 _
  Reduction = _ :& isReduction

  open isReduction {{...}} public



instance
  isCategory:Problem : isCategory (_ , ⨆ 𝑖) (Problem 𝑖)
  isCategory:Problem =
    record
    { Hom'         = Reduction
    ; isSetoid:Hom = {!!}
    ; id           = {!!}
    ; _◆_          = {!!}
    ; unit-l-◆   = {!!}
    ; unit-r-◆   = {!!}
    ; unit-2-◆   = {!!}
    ; assoc-l-◆  = {!!}
    ; assoc-r-◆  = {!!}
    ; _◈_        = {!!}
    }

𝐏𝐫𝐨𝐛 : ∀ 𝑖 -> SomeStructure
𝐏𝐫𝐨𝐛 𝑖 = structureOn (Problem 𝑖)


