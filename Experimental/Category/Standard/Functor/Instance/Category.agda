
module Verification.Experimental.Category.Standard.Functor.Instance.Category where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Standard.Category.Definition
open import Verification.Experimental.Category.Standard.Functor.Definition
open import Verification.Experimental.Category.Standard.Natural.Definition
open import Verification.Experimental.Category.Standard.Natural.Instance.Setoid



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  instance
    isCategory:Functor : isCategory _ (Functor 𝒞 𝒟)
    isCategory.Hom' isCategory:Functor = Natural
    -- isCategory.isSetoid:Hom isCategory:Functor = {!!}
    isCategory.id isCategory:Functor = {!!}
    isCategory._◆_ isCategory:Functor = {!!}
    isCategory.unit-l-◆ isCategory:Functor = {!!}
    isCategory.unit-r-◆ isCategory:Functor = {!!}
    isCategory.unit-2-◆ isCategory:Functor = {!!}
    isCategory.assoc-l-◆ isCategory:Functor = {!!}
    isCategory.assoc-r-◆ isCategory:Functor = {!!}
    isCategory._◈_ isCategory:Functor = {!!}


