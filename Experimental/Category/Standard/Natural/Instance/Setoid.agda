
module Verification.Experimental.Category.Standard.Natural.Instance.Setoid where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Standard.Category.Definition
open import Verification.Experimental.Category.Standard.Functor.Definition
open import Verification.Experimental.Category.Standard.Natural.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {F G : Functor 𝒞 𝒟} where

  _∼-Natural_ : (α β : Natural F G) -> 𝒰 _
  α ∼-Natural β = ∀{x : ⟨ 𝒞 ⟩} -> ⟨ α ⟩ {x} ∼ ⟨ β ⟩ {x}

  instance
    isEquivRel:∼-Natural : isEquivRel (∼-Base _∼-Natural_)
    isEquivRel.refl isEquivRel:∼-Natural = {!!}
    isEquivRel.sym isEquivRel:∼-Natural = {!!}
    isEquivRel._∙_ isEquivRel:∼-Natural = {!!}

  instance
    isSetoid:Natural : isSetoid _ (Hom-Base Natural F G)
    isSetoid._∼'_ isSetoid:Natural a b = ⟨ a ⟩ ∼-Natural ⟨ b ⟩
    isSetoid.isEquivRel:∼ isSetoid:Natural = {!!}

