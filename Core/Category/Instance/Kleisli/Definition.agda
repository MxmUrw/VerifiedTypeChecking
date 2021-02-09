
module Verification.Core.Category.Instance.Kleisli.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
-- open import Verification.Core.Homotopy.Level
-- open import Verification.Core.Category.Instance.Type

open import Verification.Core.Category.Monad.Definition

module _ {𝒞 : Category 𝑖} where
  module _ (T : Monad 𝒞) where
    record IKleisli (A : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ⌄ 0) where
    unquoteDecl Kleisli kleisli = #struct "Kl" (quote IKleisli) "A" Kleisli kleisli

module _ {𝒞 : Category 𝑖} where
  module _ {T : Monad 𝒞} where
    record IKleisliHom (A B : Kleisli T) (f : ⟨ A ⟩ ⟶ ⟨ ⟨ T ⟩ ⟩ ⟨ B ⟩) : 𝒰 (𝑖 ⌄ 1) where
    unquoteDecl KleisliHom kleisliHom = #struct "KlHom" (quote IKleisliHom) "f" KleisliHom kleisliHom


    instance
      IKleisli:Anything : {A : ⟨ 𝒞 ⟩} -> IKleisli T A
      IKleisli:Anything = record {}
      IKleisliHom:Anything : {A B : Kleisli T} {f : ⟨ A ⟩ ⟶ ⟨ ⟨ T ⟩ ⟩ ⟨ B ⟩} -> IKleisliHom A B f
      IKleisliHom:Anything = record {}

  -- [Definition]
  -- | The Kleisli category of a monad \AD{T} is given by:
  Category:Kleisli : ∀(T : Monad 𝒞) -> Category 𝑖
  ⟨ Category:Kleisli T ⟩ = Kleisli T
  ICategory.Hom (of Category:Kleisli T) A B = KleisliHom A B
  ICategory._≣_ (of Category:Kleisli T) f g = ⟨ f ⟩ ≣ ⟨ g ⟩
  IEquiv.refl (ICategory.IEquiv:≣ (of Category:Kleisli T)) = refl
  IEquiv.sym (ICategory.IEquiv:≣ (of Category:Kleisli T)) = sym
  IEquiv._∙_ (ICategory.IEquiv:≣ (of Category:Kleisli T)) = _∙_
  ICategory.id (of Category:Kleisli T) = ` return `
  ICategory._◆_ (of Category:Kleisli T) f g = ` ⟨ f ⟩ >=> ⟨ g ⟩ `
  ICategory.unit-l-◆ (of Category:Kleisli T) = {!!}
  ICategory.unit-r-◆ (of Category:Kleisli T) = {!!}
  ICategory.unit-2-◆ (of Category:Kleisli T) = {!!}
  ICategory.assoc-l-◆ (of Category:Kleisli T) = {!!}
  ICategory.assoc-r-◆ (of Category:Kleisli T) = {!!}
  ICategory._◈_ (of Category:Kleisli T) = {!!}
  -- //

instance
  Index-Notation:Kleisli : Index-Notation (Category 𝑖) (Monad) IAnything (∆ (Category 𝑖))
  (Index-Notation:Kleisli Index-Notation.⌄ 𝒞) T = Category:Kleisli T





