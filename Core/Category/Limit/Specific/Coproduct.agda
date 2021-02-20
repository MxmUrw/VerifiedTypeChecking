
module Verification.Core.Category.Limit.Specific.Coproduct where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Cat.Products



module _ {X : 𝒰 𝑖} {{_ : ICategory X 𝑗}} where
  record isCoproduct (a b x : X) : 𝒰 (𝑖 ､ 𝑗) where
    field ι₀ : a ⟶ x
          ι₁ : b ⟶ x
          [_,_] : {c : X} -> (f : a ⟶ c) (g : b ⟶ c) -> (x ⟶ c)
          reduce-+-₀ : ∀{c : X} -> {f : a ⟶ c} -> {g : b ⟶ c} -> ι₀ ◆ [ f , g ] ≣ f
          reduce-+-₁ : ∀{c : X} -> {f : a ⟶ c} -> {g : b ⟶ c} -> ι₁ ◆ [ f , g ] ≣ g
          expand-+   : ∀{c : X} -> {f : x ⟶ c} -> f ≣ [ ι₀ ◆ f , ι₁ ◆ f ]

  open isCoproduct {{...}} public
unquoteDecl hasCoproduct hascoproduct = #struct "isCoprod" (quote isCoproduct) "x" hasCoproduct hascoproduct

record hasCoproducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field _+_ : (a b : ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
        {{isCoproduct:+}} : ∀{a b} -> isCoproduct a b (a + b)
  infixl 100 _+_
open hasCoproducts {{...}} public

module _ {𝒞 : Category 𝑖} {{P : hasCoproducts 𝒞}} where
  Functor:+ : Functor (𝒞 ×-Cat 𝒞) 𝒞
  ⟨ Functor:+ ⟩ (a , b) = a + b
  IFunctor.map (of Functor:+) (f , g) = [ f ◆ ι₀ , g ◆ ι₁ ]
  IFunctor.functoriality-id (of Functor:+) = {!!}
  IFunctor.functoriality-◆ (of Functor:+) = {!!}
  IFunctor.functoriality-≣ (of Functor:+) = {!!}




