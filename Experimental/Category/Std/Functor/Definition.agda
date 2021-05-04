
module Verification.Experimental.Category.Std.Functor.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition




--------------------------------------------------------------------------------
-- Functors

-- [Definition]
-- | Let [..] and [..] be two categories.
module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where

-- |> A function |F|, mapping objects of |𝒞| to objects of |𝒟|
--    is called a functor [...] if the following additional data is given:
  record isFunctor (F : ⟨ 𝒞 ⟩ -> ⟨ 𝒟 ⟩) : 𝒰 (𝑖 ､ 𝑗) where

          -- | - An operation [..] mapping arrows of |𝒞| to arrows in |𝒟|.
    field map : ∀{a b : ⟨ 𝒞 ⟩} -> Hom a b -> Hom (F a) (F b)

          -- | - A proof that |map| respects equivalence.
          {{isSetoidHom:map}} : ∀{a b} -> isSetoidHom (′ Hom a b ′) (′ Hom (F a) (F b) ′) (map {a} {b})

          -- | - A proof that |map| preserves identity morphisms.
          functoriality-id : ∀{a : ⟨ 𝒞 ⟩} -> map (id {a = a}) ∼ id {a = F a}

          -- | - A proof that |map| respects composition.
          functoriality-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> map (f ◆ g) ∼ (map f) ◆ (map g)

          -- functoriality-∼ : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{f g : Hom a b} -> f ∼ g -> map f ∼ map g
-- //


-- unquoteDecl Functor functor = #struct "Fun" (quote isFunctor) "F" Functor functor
  Functor : 𝒰 _
  Functor = (⟨ 𝒞 ⟩ -> ⟨ 𝒟 ⟩) :& isFunctor


open isFunctor {{...}} public
