
module Verification.Core.Category.Instance.Opposite where

open import Verification.Conventions
open import Verification.Core.Category.Definition

-- | For a more general kind of example, consider an arbitrary category |𝒞|.
--   Then we can construct another category |𝒞 ᵒᵖ| which has the same objects
--   as |𝒞|, but where the direction of all arrows is reversed.

-- [Definition]
-- | There is a function [..], mapping a category to its opposite. It is defined as:
_ᵒᵖ : Category 𝑖 -> Category 𝑖
⟨ 𝒞 ᵒᵖ ⟩                         = ⟨ 𝒞 ⟩
ICategory.Hom (of 𝒞 ᵒᵖ) a b  = Hom {{of 𝒞}} b a

-- |> All equations for |𝒞 ᵒᵖ| can be proven by simply using their symmetric counterpart in $𝒞$.
ICategory._≣_        (of 𝒞 ᵒᵖ)  = _≣_
ICategory.IEquiv:≣   (of 𝒞 ᵒᵖ)  = IEquiv:≣
ICategory.id         (of 𝒞 ᵒᵖ)  = id
ICategory._◆_        (of 𝒞 ᵒᵖ)  = λ f g -> g ◆ f
ICategory._◈_        (of 𝒞 ᵒᵖ)  = λ p q -> q ◈ p
ICategory.unit-l-◆   (of 𝒞 ᵒᵖ)  = unit-r-◆
ICategory.unit-r-◆   (of 𝒞 ᵒᵖ)  = unit-l-◆
ICategory.unit-2-◆   (of 𝒞 ᵒᵖ)  = unit-2-◆
ICategory.assoc-l-◆  (of 𝒞 ᵒᵖ)  = assoc-r-◆
ICategory.assoc-r-◆  (of 𝒞 ᵒᵖ)  = assoc-l-◆
-- //
