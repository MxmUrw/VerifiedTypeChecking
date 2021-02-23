
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

record IIdxSetHom {K : 𝒰 𝑘} (A : IdxSet K 𝑖) (B : IdxSet K 𝑗) (f : ∀{k : K} -> ⟨ A ⟩ k -> ⟨ B ⟩ k) : 𝒰 (𝑖 ､ 𝑗) where

instance
  IIdxSetHom:Anything : {K : 𝒰 𝑘} {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} {f : ∀{k : K} -> ⟨ A ⟩ k -> ⟨ B ⟩ k} -> IIdxSetHom A B f
  IIdxSetHom:Anything = record {}

open IIdxSetHom {{...}} public
unquoteDecl IdxSetHom idxSetHom = #struct "IdxStHom" (quote IIdxSetHom) "f" IdxSetHom idxSetHom

module _ {K : 𝒰 𝑘} where
  record is-≣-IdxSet {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} (f g : IdxSetHom A B) (P : ∀{k} x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x) : 𝒰 (𝑖 ､ 𝑗) where

  instance
    is-≣-IdxSet-Anything : {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} {f g : IdxSetHom A B} {P : ∀{k} x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x} -> is-≣-IdxSet f g P
    is-≣-IdxSet-Anything = record {}


open is-≣-IdxSet {{...}} public
unquoteDecl _≣-IdxSet_ mk-≣-IdxSet = #struct "_≣_" (quote is-≣-IdxSet) "P" _≣-IdxSet_ mk-≣-IdxSet

module _ {K : 𝒰 𝑘} where
  instance
    IEquiv:≣-IdxSet : {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} -> IEquiv (_≣-IdxSet_ {A = A} {B = B})
    ⟨ IEquiv.refl IEquiv:≣-IdxSet ⟩ _ = refl
    ⟨ IEquiv.sym IEquiv:≣-IdxSet p ⟩ x = ⟨ p ⟩ x ⁻¹
    ⟨ IEquiv._∙_ IEquiv:≣-IdxSet p q ⟩ x = ⟨ p ⟩ x ∙ ⟨ q ⟩ x

instance
  IEquiv:≣-on-IdxSet : {K : 𝒰 𝑘} {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} -> IEquiv (λ (f g : IdxSetHom A B) -> ∀{k} -> ∀ x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x)
  IEquiv.refl IEquiv:≣-on-IdxSet x = refl
  IEquiv.sym IEquiv:≣-on-IdxSet p x₁ = p _ ⁻¹
  IEquiv._∙_ IEquiv:≣-on-IdxSet p q _ = p _ ∙ q _



Category:IdxSet : ∀(K : 𝒰 𝑘) -> ∀ 𝑖 -> Category (𝑖 ⁺ ⊔ 𝑘 , (𝑘 ⊔ 𝑖) , (𝑘 ⊔ 𝑖))
⟨ Category:IdxSet K 𝑖 ⟩ = IdxSet K 𝑖
ICategory.Hom (of Category:IdxSet K 𝑖) = IdxSetHom
ICategory._≣_ (of Category:IdxSet K 𝑖) f g = ∀{k} -> ∀ x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x
-- f ≣-IdxSet g -- 
-- ∀ {k} x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x
ICategory.IEquiv:≣ (of Category:IdxSet K 𝑖) = IEquiv:≣-on-IdxSet
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


