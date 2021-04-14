
module Verification.Experimental.Data.Prop.Instance.Setoid where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Data.Universe.Definition

instance
  isSetoid:Prop : isSetoid _ (Prop 𝑖)
  isSetoid._∼'_ isSetoid:Prop A B = (⟨ A ⟩ -> ⟨ B ⟩) ×-𝒰 (⟨ B ⟩ -> ⟨ A ⟩)
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:Prop) = incl (id-𝒰 , id-𝒰)
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:Prop) (incl (p , q)) = incl (q , p)
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:Prop) (incl (p , q)) (incl (v , w)) = incl (p ◆-𝒰 v , w ◆-𝒰 q)



