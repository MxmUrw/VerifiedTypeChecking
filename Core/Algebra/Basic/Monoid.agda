
{-# OPTIONS --cubical --allow-unsolved-metas --no-import-sorts #-}

module Verification.Core.Algebra.Basic.Monoid where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Homotopy.Level
-- open import Verification.Core.Category.Instance.Type


-- ===* Monoids
-- | Monoids are an important concept in both mathematics and computer science.

-- [Definition]
-- | A type |A| has the structure of a monoid,
record IMonoid (A : 𝒰 𝑖) : 𝒰 𝑖 where

-- | - if there is a special element [..], and a multiplication operation [..].
  field 𝟷    : A
        _⋅_  : A -> A -> A

-- | - Such that the operation is associative,
        assoc-⋅   : ∀{a b c : A} -> (a ⋅ b) ⋅ c ≡ a ⋅ (b ⋅ c)

-- |>  and |𝟷| is a left and right unit for it.
        unit-l-⋅  : ∀{a : A} -> 𝟷 ⋅ a ≡ a
        unit-r-⋅  : ∀{a : A} -> a ⋅ 𝟷 ≡ a

  infixl 50 _⋅_
-- //


-- [Hide]
open IMonoid {{...}} public
unquoteDecl Monoid monoid = #struct "Mon" (quote IMonoid) "A" Monoid monoid

record IMonoidHom (M : Monoid 𝑖) (N : Monoid 𝑗) (f : ⟨ M ⟩ -> ⟨ N ⟩) : 𝒰 (𝑖 ⊔ 𝑗) where

unquoteDecl MonoidHom monoidHom = #struct "MonHom" (quote IMonoidHom) "f" MonoidHom monoidHom

instance
  ICategory:Monoid : ICategory (Monoid 𝑖) (𝑖 , 𝑖)
  ICategory.Hom ICategory:Monoid = MonoidHom
  ICategory._≣_ ICategory:Monoid = {!!}
  ICategory.IEquiv:≣ ICategory:Monoid = {!!}
  ICategory.id ICategory:Monoid = {!!}
  ICategory._◆_ ICategory:Monoid = {!!}
  ICategory._◈_ ICategory:Monoid = {!!}
  ICategory.unit-l-◆ ICategory:Monoid = {!!}
  ICategory.unit-r-◆ ICategory:Monoid = {!!}
  ICategory.unit-2-◆ ICategory:Monoid = {!!}
  ICategory.assoc-l-◆ ICategory:Monoid = {!!}
  ICategory.assoc-r-◆ ICategory:Monoid = {!!}


instance
  IMonoidHom:⋅ : {M : Monoid 𝑖} -> ∀{r : ⟨ M ⟩} -> IMonoidHom M M (r ⋅_)
  IMonoidHom:⋅ = record {}

-- //

-- record IMonoid⍮Com (A : 𝒰 𝑖) : 𝒰 𝑖 where
--   field {{Impl}} : IMonoid A
--         commute : ∀{a b : A} -> a ⋅ b ≡ b ⋅ a


-------------------------
-- Instances

-- instance
--   ISet:List : ∀{A : 𝒰 𝑖} {{_ : ISet A}} -> ISet (List A)
--   ISet:List = {!!}


-- [Example]
-- | For every set $A$, we can build the free monoid on it.
Monoid:Free : 𝒰 𝑖 -> Monoid 𝑖
-- | Its underlying set consists of lists with entries in $A$:
⟨ Monoid:Free A ⟩                = List A
-- | The neutral element is $\AF{???}$, and multiplication is given by concatenation of lists.
IMonoid.𝟷       (of Monoid:Free A)  = []
IMonoid._⋅_     (of Monoid:Free A)  = λ xs ys -> xs ++-List ys
IMonoid.assoc-⋅   (of Monoid:Free A)  = {!!}
IMonoid.unit-l-⋅  (of Monoid:Free A)  = {!!}
IMonoid.unit-r-⋅  (of Monoid:Free A)  = {!!}
-- //

instance IMonoid:Free = #openstruct Monoid:Free








