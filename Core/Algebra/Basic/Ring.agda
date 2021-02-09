

{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Algebra.Basic.Ring where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Algebra.Basic.Monoid
open import Verification.Core.Algebra.Basic.Abelian


-- ===* Rings
-- | We define rings as sets with compatible abelian and monoid structures.

-- [Hide]

record IRing (R : 𝒰 𝑖) : 𝒰 𝑖 where
  field {{Multiplicative}} : IMonoid R
        {{Additive}} : IAbelian R
unquoteDecl Ring ring = #struct "Ring" (quote IRing) "R" Ring ring

record IRingHom (R : Ring 𝑖) (S : Ring 𝑗) (f : ⟨ R ⟩ -> ⟨ S ⟩) : 𝒰 (𝑖 ⊔ 𝑗) where

unquoteDecl RingHom ringhom = #struct "RingHom" (quote IRingHom) "f" RingHom ringhom

instance
  ICategory:Ring : ICategory (Ring 𝑖) (𝑖 , 𝑖)
  ICategory.Hom ICategory:Ring = RingHom
  ICategory._≣_ ICategory:Ring = {!!}
  ICategory.IEquiv:≣ ICategory:Ring = {!!}
  ICategory.id ICategory:Ring = {!!}
  ICategory._◆_ ICategory:Ring = {!!}
  ICategory._◈_ ICategory:Ring = {!!}
  ICategory.unit-l-◆ ICategory:Ring = {!!}
  ICategory.unit-r-◆ ICategory:Ring = {!!}
  ICategory.unit-2-◆ ICategory:Ring = {!!}
  ICategory.assoc-l-◆ ICategory:Ring = {!!}
  ICategory.assoc-r-◆ ICategory:Ring = {!!}


instance
  IAbelianHom:scale : {R : 𝒰 𝑖} {{_ : IRing R}} -> ∀{r : R} -> IAbelianHom (⌘ R) (⌘ R) (r ⋅_)
  unwrap IAbelianHom:scale = record {}

AbelianHom:scale : {R : Ring 𝑖} -> ∀(r : ⟨ R ⟩) -> AbelianHom (⌘ ⟨ R ⟩) (⌘ ⟨ R ⟩)
⟨ AbelianHom:scale r ⟩ = r ⋅_
(of (AbelianHom:scale r)) = IAbelianHom:scale


-- //

