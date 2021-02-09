
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Category.Instance.Type where

open import Verification.Conventions
open import Verification.Core.Category.Definition

-------------------------
-- The Category of Types

-- | The archetypal example of a category is |Category:Set|, the category of sets.
--   In cubical type theory, since here types are more general than mere sets,
--   we have the distinct notion of the category of types, |Category:𝒰|.

-- | Even though |Category:Set| is better behaved, and also more important further on,
--   we begin by presenting the very straightforward definition of |Category:𝒰|.

-- [Example]
-- | The category of types [..] is defined as follows:
Category:𝒰 : (𝑖 : 𝔏) -> Category (𝑖 ⁺ , 𝑖 , 𝑖)

-- | - The identity morphisms [..] are given by [..].
id-𝒰 : ∀{A : 𝒰 𝑖} -> A -> A
id-𝒰 a = a

-- | - Let [..], [..] and [..] be types.
module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
-- |> Then composition is given by:
    comp-𝒰 : (f : A -> B) -> (g : B -> C) -> (A -> C)
    comp-𝒰 f g a = g (f a)

-- | - Finally we combine everything together:
-- |   1. The underlying type is [..].
⟨ Category:𝒰 𝑖 ⟩ = 𝒰 𝑖
-- |   2. The homs are [..].
ICategory.Hom (of Category:𝒰 𝑖) = λ A B -> A -> B
ICategory._≣_ (of Category:𝒰 𝑖) = _≡_
ICategory.IEquiv:≣ (of Category:𝒰 𝑖) = IEquiv:Path
ICategory.id (of Category:𝒰 𝑖) = id-𝒰
ICategory._◆_ (of Category:𝒰 𝑖) = comp-𝒰
ICategory.unit-l-◆ (of Category:𝒰 𝑖) = refl
ICategory.unit-r-◆ (of Category:𝒰 𝑖) = refl
ICategory.unit-2-◆ (of Category:𝒰 𝑖) = refl
ICategory.assoc-l-◆ (of Category:𝒰 𝑖) = refl
ICategory.assoc-r-◆ (of Category:𝒰 𝑖) = refl
ICategory._◈_ (of Category:𝒰 𝑖) = λ p q i -> comp-𝒰 (p i) (q i)
-- //
instance ICategory:𝒰 = #openstruct Category:𝒰





-- data ELevel : 𝒰ω where
--   finite : ULevel -> ELevel
--   ∞ : ELevel

-- get : ELevel -> 𝒰ω₂
-- get (finite x) = Lift (𝒰 x)
-- get ∞ = {!!}

-- data 𝒰∞ : 𝒰ω where
--   type : (l : ULevel) -> (𝒰 l) -> 𝒰∞

-- test : 𝒰ω2
-- test = 𝒰∞

-- Universe : ℕ -> 

-- ICategory:𝒰∞ : ICategory 𝒰∞ ?
-- ICategory:𝒰∞ = ?




