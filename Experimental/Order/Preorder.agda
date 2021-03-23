
module Verification.Experimental.Order.Preorder where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Type
open import Verification.Experimental.Meta.Structure

--------------------------------------------------------------------
-- == Preorder

record isPreorder (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field _≤_ : A -> A -> 𝒰 𝑖
        refl-≤ : {a : A} -> a ≤ a
        trans-≤ : {a b c : A} -> a ≤ b -> b ≤ c -> a ≤ c
open isPreorder {{...}} public

Preorder : ∀ 𝑖 -> 𝒰 (𝑖 ⁺)
Preorder 𝑖 = 𝒰 𝑖 :& isPreorder

instance
  isPreorder:ℕ : isPreorder ℕ
  isPreorder._≤_ isPreorder:ℕ = _≤-ℕ_
  isPreorder.refl-≤ isPreorder:ℕ = refl-≤-ℕ
  isPreorder.trans-≤ isPreorder:ℕ = trans-≤-ℕ

Preorder:ℕ : Preorder _
Preorder:ℕ = make& ℕ

{-
unquoteDecl Preorder preorder = #struct "PreOrd" (quote isPreorder) "A" Preorder preorder

-}


-- record isMonotone {A : Preorder 𝑖} {B : Preorder 𝑗} (f : El A -> El B) : 𝒰 (𝑖 ､ 𝑗) where
--   field monotone : ∀{a b : El A} -> (a ≤ b) -> f a ≤ f b

record isMonotone {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : Preorder 𝑖 on A}} {{_ : Preorder 𝑗 on B}} (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
  field monotone : ∀{a b : A} -> (a ≤ b) -> f a ≤ f b


{-
record isMonotone {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isPreorder A}} {{_ : isPreorder B}} (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
  field monotone : ∀{a b : A} -> (a ≤ b) -> f a ≤ f b

Monotone : (A : Preorder 𝑖) (B : Preorder 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
Monotone A B = (El A -> El B) :& isMonotone
-- unquoteDecl Monotone makeMonotone = #struct "Monotone" (quote isMonotone) "f" Monotone makeMonotone

Category:Preorder : (𝑖 : 𝔏) -> Category _
⟨ Category:Preorder 𝑖 ⟩ = Preorder 𝑖
ICategory.Hom (of Category:Preorder 𝑖) = Monotone
ICategory._≣_ (of Category:Preorder 𝑖) f g = El f ≡ El g
ICategory.IEquiv:≣ (of Category:Preorder 𝑖) = {!!}
ICategory.id (of Category:Preorder 𝑖) = {!!}
ICategory._◆_ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-l-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-r-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-2-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.assoc-l-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.assoc-r-◆ (of Category:Preorder 𝑖) = {!!}
ICategory._◈_ (of Category:Preorder 𝑖) = {!!}
-}

{-
module _ {A : 𝒰 𝑖} {{_ : isPreorder A}} where
  infix 30 _<_
  _<_ : A -> A -> 𝒰 𝑖
  a < b = (a ≤ b) ×-𝒰 (a ≡ b -> 𝟘-𝒰)

  instance
    Cast:≡→≤ : ∀{a b : A} -> Cast (a ≡ b) IAnything (a ≤ b)
    Cast.cast (Cast:≡→≤ {a = a} {b}) e = transport (λ i -> e (~ i) ≤ b) refl-≤


-- record isPreorderHom {A B : Preorder} (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰₀ where

-- record PreorderHom (A B : Preorder) : 𝒰₀ where

instance
  -- ICategory:Preorder : ICategory Preorder (𝑖 , 𝑖 ,-)
  -- ICategory:Preorder = {!!}
{-
  ICategory.Hom ICategory:Preorder = PreorderHom
  ICategory.id ICategory:Preorder = {!!}
  ICategory._◆_ ICategory:Preorder = {!!}
-}

  isPreorder:ℕ : isPreorder ℕ
  isPreorder._≤_ isPreorder:ℕ = _≤-ℕ_
  isPreorder.refl-≤ isPreorder:ℕ = refl-≤-ℕ
  isPreorder.trans-≤ isPreorder:ℕ = trans-≤-ℕ




--------------------------------------------------------------------
-- == Concatenation of preorders

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{_ : isPreorder A}} {{_ : isPreorder B}} where

  data _≤-⊕_ : (a b : A +-𝒰 B) -> 𝒰 𝑖 where
    left-≤ : ∀{a b : A} -> a ≤ b -> left a ≤-⊕ left b
    right-≤ : ∀{a b : B} -> a ≤ b -> right a ≤-⊕ right b
    left-right-≤ : ∀{a : A} {b : B} -> left a ≤-⊕ right b


  trans-≤-⊕ : ∀{a b c} -> (a ≤-⊕ b) -> (b ≤-⊕ c) -> a ≤-⊕ c
  trans-≤-⊕ (left-≤ p) (left-≤ q) = left-≤ (trans-≤ p q)
  trans-≤-⊕ (left-≤ x) left-right-≤ = left-right-≤
  trans-≤-⊕ (right-≤ p) (right-≤ q) = right-≤ (trans-≤ p q)
  trans-≤-⊕ left-right-≤ (right-≤ x) = left-right-≤

  refl-≤-⊕ : ∀{a} -> (a ≤-⊕ a)
  refl-≤-⊕ {left x} = left-≤ refl-≤
  refl-≤-⊕ {just x} = right-≤ refl-≤


  instance
    isPreorder:+ : isPreorder (A +-𝒰 B)
    isPreorder._≤_ isPreorder:+ = _≤-⊕_
    isPreorder.refl-≤ isPreorder:+ {a = a} = refl-≤-⊕ {a}
    isPreorder.trans-≤ isPreorder:+ {a = a} = trans-≤-⊕ {a = a}


_⊕-Preorder_ : Preorder 𝑖 -> Preorder 𝑖 -> Preorder 𝑖
A ⊕-Preorder B = preorder (⟨ A ⟩ +-𝒰 ⟨ B ⟩)

instance
  INotation:DirectSum:Preorder : INotation:DirectSum (Preorder 𝑖)
  INotation:DirectSum._⊕_ INotation:DirectSum:Preorder = _⊕-Preorder_


--------------------------------------------------------------------
-- == Example instances

instance
  isPreorder:⊤ : ∀{𝑖} -> isPreorder (Lift {j = 𝑖} 𝟙-𝒰)
  isPreorder._≤_ isPreorder:⊤ a b = `𝟙`
  isPreorder.refl-≤ isPreorder:⊤ = lift tt
  isPreorder.trans-≤ isPreorder:⊤ a b = lift tt

-}
