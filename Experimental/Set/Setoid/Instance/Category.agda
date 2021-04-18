
module Verification.Experimental.Set.Setoid.Instance.Category where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Standard.Category.Definition


instance
  isCategory:Setoid : ∀{𝑗 : 𝔏 ^ 2} -> isCategory _ (Setoid 𝑗)
  isCategory.Hom (isCategory:Setoid {𝑗}) = SetoidHom
  isCategory.id (isCategory:Setoid {𝑗}) = {!!}
  isCategory._◆_ (isCategory:Setoid {𝑗}) = {!!}
  isCategory.unit-l-◆ (isCategory:Setoid {𝑗}) = {!!}
  isCategory.unit-r-◆ (isCategory:Setoid {𝑗}) = {!!}
  isCategory.unit-2-◆ (isCategory:Setoid {𝑗}) = {!!}
  isCategory.assoc-l-◆ (isCategory:Setoid {𝑗}) = {!!}
  isCategory.assoc-r-◆ (isCategory:Setoid {𝑗}) = {!!}
  isCategory._◈_ (isCategory:Setoid {𝑗}) = {!!}



