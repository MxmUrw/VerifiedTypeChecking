
module Verification.Experimental.Algebra.MonoidWithZero.Ideal where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition


record isIdeal-r {𝑗 : 𝔏 ^ 2} (A : Monoid₀ 𝑗) (P : 𝒫 ⟨ A ⟩ :& isSubsetoid) : 𝒰 𝑗 where
  field ideal-◍ : ⟨ ⟨ P ⟩ ◍ ⟩
  field ideal-r-⋆ : ∀{a} -> ⟨ ⟨ P ⟩ a ⟩ -> ∀ b -> ⟨ ⟨ P ⟩ (a ⋆ b) ⟩
open isIdeal-r {{...}} public

Ideal-r : (A : Monoid₀ 𝑗) -> 𝒰 _
Ideal-r A = _ :& isIdeal-r A



module _ {A : Monoid₀ (𝑖 , 𝑖)} where
  instance
    isSetoid:Ideal-r : isSetoid _ (Ideal-r A)
    isSetoid:Ideal-r = isSetoid:hasU

  _↷-Ide'_ : (a : ⟨ A ⟩) -> (I : Ideal-r A) -> 𝒫 ⟨ A ⟩
  _↷-Ide'_ a I = λ b -> ∣ (∑ λ x -> ⟨ ⟨ I ⟩ x ⟩ ×-𝒰 (b ∼ a ⋆ x)) ∣

  module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩} {{_ : Ideal-r A on I}} where
    instance
      isSubsetoid:↷-Ide' : isSubsetoid (a ↷-Ide' ′ I ′)
      isSubsetoid.transp-Subsetoid isSubsetoid:↷-Ide' {b} {c} p (x , Ix , q) = (x , Ix , p ⁻¹ ∙ q)

    instance
      isIdeal-r:↷-Ide' : isIdeal-r A ′(a ↷-Ide' ′ I ′)′
      isIdeal-r.ideal-◍   isIdeal-r:↷-Ide' = {!!}
      isIdeal-r.ideal-r-⋆ isIdeal-r:↷-Ide' = {!!}

  _↷-Ide_ : (a : ⟨ A ⟩) -> (I : Ideal-r A) -> Ideal-r A
  _↷-Ide_ a I = ′(a ↷-Ide' I)′

  instance
    hasAction-l:Ideal-r : hasAction-l ′ ⟨ A ⟩ ′ ′ Ideal-r A ′
    hasAction-l._↷_ hasAction-l:Ideal-r = _↷-Ide_
    hasAction-l.assoc-l-↷ hasAction-l:Ideal-r = {!!}

  instance
    isIdeal-r:⊤ : isIdeal-r A ⊤
    isIdeal-r.ideal-◍ isIdeal-r:⊤ = tt
    isIdeal-r.ideal-r-⋆ isIdeal-r:⊤ _ _ = tt




module _ {𝑖 : 𝔏} {A : Monoid₀ (𝑖 , 𝑖)} where

  record isPrincipal-r (I : Ideal-r A) : 𝒰 (𝑖 ⁺) where
    field rep : ⟨ A ⟩
    field principal-r : I ∼ (rep ↷ ′ ⊤ ′)
  open isPrincipal-r {{...}} public

  Principal-r::rep-in-ideal : ∀{I : Ideal-r A} -> {{_ : isPrincipal-r I}} -> ⟨ ⟨ I ⟩ rep ⟩
  Principal-r::rep-in-ideal {I} =
    let P₀ = inv-∼-Setoid ⟨ ⟨ principal-r ⟩ ⟩ (◌ , tt , unit-r-⋆ ⁻¹)
    in P₀

Principal-r : (Monoid₀ (𝑖 , 𝑖)) -> 𝒰 _
Principal-r A = Ideal-r A :& isPrincipal-r

module _ {𝑖 : 𝔏} {A : Monoid₀ (𝑖 , 𝑖)} where
  record isPrincipal⁺-r (I : Principal-r A) : 𝒰 𝑖 where
    field zeroOrCancel-r : (rep ∼ ◍) +-𝒰 ((rep ≁ ◍) ×-𝒰 ∀{b c : ⟨ A ⟩} -> rep ⋆ b ∼ rep ⋆ c -> b ∼ c)
  open isPrincipal⁺-r {{...}} public

  isPrincipal/⁺-r : (I : Ideal-r A) -> 𝒰 _
  isPrincipal/⁺-r = isPrincipal-r :> isPrincipal⁺-r

  -- isPrincipal-r : (I : Ideal-r A) -> 𝒰 _
  -- isPrincipal-r I = 




-- record hasUniqueSolution {A : 𝒰 𝑖} {{_ : isSetoid 𝑗 A}} (P : A -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
--   field ⟨_⟩ : ∑ P
--   field isUniqueSolution : ∀(x : ∑ P) -> fst x ∼ fst ⟨_⟩




