
module Verification.Experimental.Category.Standard.Category.Instance.Category where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Category.Standard.Category.Definition
open import Verification.Experimental.Category.Standard.Functor.Definition
open import Verification.Experimental.Category.Standard.Functor.Instance.Category
open import Verification.Experimental.Category.Standard.Natural.Definition
open import Verification.Experimental.Category.Standard.Natural.Instance.Setoid
open import Verification.Experimental.Category.Standard.Morphism.Iso

isSetoid:Hom-Base : {A : 𝒰 𝑖} {Hom : A -> A -> 𝒰 𝑗} -> ∀{a b}
                    -> {{_ : isSetoid 𝑘 (Hom a b)}}
                    -> isSetoid _ (Hom-Base Hom a b)
isSetoid._∼'_ (isSetoid:Hom-Base {{P}}) f g = _∼_ {{P}} ⟨ f ⟩ ⟨ g ⟩
isSetoid.isEquivRel:∼ isSetoid:Hom-Base = {!!}

all : 𝔏 ^ 3 -> 𝔏
all (i , j , k) = i ⊔ j ⊔ k

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory 𝑗 𝒞}} where
  instance
    isFunctor:id : isFunctor ′ 𝒞 ′ ′ 𝒞 ′ id-𝒰
    isFunctor.map isFunctor:id = id-𝒰
    isFunctor.isSetoidHom:map isFunctor:id = {!!}
    isFunctor.functoriality-id isFunctor:id = {!!}
    isFunctor.functoriality-◆ isFunctor:id = {!!}


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {𝒢 : Category 𝑘} where
  _◆-Cat_ : (Functor 𝒞 𝒟) -> Functor 𝒟 𝒢 -> Functor 𝒞 𝒢
  _◆-Cat_ F G = {!!}
    -- isFunctor:◆ : isFunctor ′ 
  -- id-Functor : Functor 𝒞 𝒞
  -- id-Functor = {!!}

instance
  isCategory:Category : ∀{𝑗 : 𝔏 ^ 3} -> isCategory (_) (Category 𝑗)
  isCategory.Hom' isCategory:Category = Functor
  isCategory.isSetoid:Hom (isCategory:Category {𝑗}) = isSetoid:Hom-Base
  isCategory.id isCategory:Category = incl ′ id-𝒰 ′
  isCategory._◆_ isCategory:Category = {!!}
  isCategory.unit-l-◆ isCategory:Category = {!!}
  isCategory.unit-r-◆ isCategory:Category = {!!}
  isCategory.unit-2-◆ isCategory:Category = {!!}
  isCategory.assoc-l-◆ isCategory:Category = {!!}
  isCategory.assoc-r-◆ isCategory:Category = {!!}
  isCategory._◈_ isCategory:Category = {!!}

