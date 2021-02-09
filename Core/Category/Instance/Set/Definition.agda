

module Verification.Core.Category.Instance.Set.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Homotopy.Level
open import Verification.Core.Category.Instance.Type

-- | In order to define |Category:Set|, we need to say what a set is.
--   Since the notion of the homotopy level of a type is already defined,
--   we merely say:

-- [Definition]
-- | The type [..] of sets contains all types which have homotopy level 2, i.e., [..].
Set : (𝑖 : 𝔏) -> 𝒰 (𝑖 ⁺)
Set 𝑖 = HType 2 𝑖
-- //

-- | This allows us to define the category of sets:

-- [Example]
-- | The category of sets [..] is given by:
Category:Set : (𝑖 : 𝔏) -> Category (𝑖 ⁺ , 𝑖 , 𝑖)

-- | - The underlying type is [..].
⟨ Category:Set 𝑖 ⟩ = Set 𝑖

-- | - Arrows between two sets |A| and |B| are simply functions |A → B|.
--     But for better type inference we wrap them in a newtype, [..].
ICategory.Hom (of Category:Set 𝑖) A B = HTypeHom A B

-- | - Equality of arrows is given by equality of the underlying functions:
ICategory._≣_ (of Category:Set 𝑖) f g = ∀ x -> ⟨ f ⟩ x ≡ ⟨ g ⟩ x

-- |>  As this is the usual path type, it is an equivalence relation:
IEquiv.refl  (ICategory.IEquiv:≣ (of Category:Set 𝑖)) = λ x -> refl
IEquiv.sym   (ICategory.IEquiv:≣ (of Category:Set 𝑖)) p = λ x -> sym (p x)
IEquiv._∙_   (ICategory.IEquiv:≣ (of Category:Set 𝑖)) p q = λ x -> p x ∙ q x

-- | - Identity and composition are inherited from |Category:𝒰|
ICategory.id   (of Category:Set 𝑖) = ` id-𝒰 `
ICategory._◆_  (of Category:Set 𝑖) f g = ` comp-𝒰 ⟨ f ⟩ ⟨ g ⟩ `

-- | - All equations hold trivially as well.
ICategory.unit-l-◆    (of Category:Set 𝑖) x = refl
ICategory.unit-r-◆    (of Category:Set 𝑖) x = refl
ICategory.unit-2-◆    (of Category:Set 𝑖) x = refl
ICategory.assoc-l-◆   (of Category:Set 𝑖) x = refl
ICategory.assoc-r-◆   (of Category:Set 𝑖) x = refl
ICategory._◈_         (of Category:Set 𝑖) p q x = λ i -> (q (p x i) i)
-- //


instance ICategory:Set = #openstruct Category:Set






