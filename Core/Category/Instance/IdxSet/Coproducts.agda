
module Verification.Core.Category.Instance.IdxSet.Coproducts where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Functor.Adjunction
open import Verification.Core.Category.Limit.Specific
-- open import Verification.Core.Category.Limit.Kan.Definition
open import Verification.Core.Category.Limit.Kan.Terminal
-- open import Verification.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Core.Category.Limit.Kan.Product
-- open import Verification.Core.Category.Limit.Definition
-- open import Verification.Core.Category.Limit.Product
-- open import Verification.Core.Category.Limit.Equalizer
-- open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Category.Lift
open import Verification.Core.Homotopy.Level

open import Verification.Core.Category.Instance.IdxSet.Definition

module _ {K : 𝒰 𝑘} where
  _+-IdxSet_ : IdxSet K 𝑖 -> IdxSet K 𝑖 -> IdxSet K (𝑖)
  ⟨ A +-IdxSet B ⟩ k = ⟨ A ⟩ k +-𝒰 ⟨ B ⟩ k
  IIdxSet.ISet:this (of (A +-IdxSet B)) = {!!}




--------------------------------------------------------------------
-- IdxSet has coproducts

  -- private
  --   P : Functor `(`𝟚` ⟶ (` IdxSet K 𝑖 `))` (` 𝟙 ⟶ (` IdxSet K 𝑖 `)`)
  --   ⟨ P ⟩ D = Diagram-𝟙 (⟨ D ⟩ (↥ ₀) +-IdxSet ⟨ D ⟩ (↥ ₁))
  --   IFunctor.map (of P) = {!!}
  --   IFunctor.functoriality-id (of P) = {!!}
  --   IFunctor.functoriality-◆ (of P) = {!!}
  --   IFunctor.functoriality-≣ (of P) = {!!}

  instance
    hasCoproducts:IdxSet : hasCoproducts (` IdxSet K 𝑖 `)
    hasCoproducts:IdxSet = {!!}
    -- ⟨ hasCoproducts:IdxSet ⟩ = P
    -- IAdjoint.embed (of hasCoproducts:IdxSet) = {!!}
    -- IAdjoint.eval (of hasCoproducts:IdxSet) = {!!}
    -- IAdjoint.reduce-Adj-β (of hasCoproducts:IdxSet) = {!!}
    -- IAdjoint.reduce-Adj-η (of hasCoproducts:IdxSet) = {!!}

