
module Verification.Core.Category.Instance.IdxSet.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Proper
open import Verification.Core.Homotopy.Level
open import Verification.Core.Category.Instance.Type


record IIdxSet (K : 𝒰 𝑖) {𝑗} (A : K -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field {{ISet:this}} : ∀{k : K} -> ISet (A k)
open IIdxSet {{...}} public
unquoteDecl IdxSet idxSet = #struct "IdxSt" (quote IIdxSet) "A" IdxSet idxSet

module _ {K : 𝒰 𝑘} where
  record IIdxSetHom (A : IdxSet K 𝑖) (B : IdxSet K 𝑗) (f : ∀{k : K} -> ⟨ A ⟩ k -> ⟨ B ⟩ k) : 𝒰 (𝑖 ､ 𝑗) where

  instance
    IIdxSetHom:Anything : {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} {f : ∀{k : K} -> ⟨ A ⟩ k -> ⟨ B ⟩ k} -> IIdxSetHom A B f
    IIdxSetHom:Anything = record {}


open IIdxSetHom {{...}} public
unquoteDecl IdxSetHom idxSetHom = #struct "IdxStHom" (quote IIdxSetHom) "f" IdxSetHom idxSetHom


Category:IdxSet : ∀(K : 𝒰 𝑘) -> ∀ 𝑖 -> Category (𝑖 ⁺ ⊔ 𝑘 , (𝑘 ⊔ 𝑖) , (𝑘 ⊔ 𝑖))
⟨ Category:IdxSet K 𝑖 ⟩ = IdxSet K 𝑖
ICategory.Hom (of Category:IdxSet K 𝑖) = IdxSetHom
ICategory._≣_ (of Category:IdxSet K 𝑖) f g = ∀ {k} x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x
ICategory.IEquiv:≣ (of Category:IdxSet K 𝑖) = {!!}
ICategory.id (of Category:IdxSet K 𝑖) = idxSetHom (id)
ICategory._◆_ (of Category:IdxSet K 𝑖) f g = ` (λ {k} -> ⟨ f ⟩ {k} ◆ ⟨ g ⟩ {k}) `
ICategory.unit-l-◆ (of Category:IdxSet K 𝑖) = {!!}
ICategory.unit-r-◆ (of Category:IdxSet K 𝑖) = {!!}
ICategory.unit-2-◆ (of Category:IdxSet K 𝑖) = {!!}
ICategory.assoc-l-◆ (of Category:IdxSet K 𝑖) = {!!}
ICategory.assoc-r-◆ (of Category:IdxSet K 𝑖) = {!!}
ICategory._◈_ (of Category:IdxSet K 𝑖) = {!!}

instance ICategory:IdxSet = #openstruct Category:IdxSet

module _ {K : 𝒰 𝑘} where
  instance
    I1Category:IdxSet : I1Category (Category:IdxSet K 𝑗)
    I1Category:IdxSet = {!!}


