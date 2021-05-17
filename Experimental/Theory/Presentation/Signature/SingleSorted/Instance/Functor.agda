
module Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Instance.Functor where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Definition
open import Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Instance.Setoid


TermF : ∀ (𝑖 : 𝔏 ^ 2) -> ∀(σ : Signature) -> Setoid (𝑖 ⌄ 0 , 𝑖 ⌄ 1) -> Setoid (𝑖 ⌄ 0 , (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1))
TermF _ σ A = ′ Term σ ⟨ A ⟩ ′

module _ {σ : Signature} {A B : Setoid 𝑖} where
  mutual
    map-Term : (f : SetoidHom A B) -> Term σ ⟨ A ⟩ -> Term σ ⟨ B ⟩
    map-Term f (te a ts) = te a (map-Terms f ts)
    map-Term f (var x) = var (⟨ f ⟩ x)

    map-Terms : (f : SetoidHom A B) -> Terms σ ⟨ A ⟩ n -> Terms σ ⟨ B ⟩ n
    map-Terms f [] = []
    map-Terms f (t ∷ ts) = map-Term f t ∷ map-Terms f ts

  instance
    isSetoidHom:map-Term : ∀{f : SetoidHom A B} -> isSetoidHom (TermF 𝑖 σ A) (TermF 𝑖 σ B) (map-Term f)
    isSetoidHom.preserves-∼ isSetoidHom:map-Term = {!!}


instance
  isFunctor:TermF : ∀{σ : Signature} -> isFunctor (Std _) (Std _) (TermF 𝑖 σ)
  isFunctor.map (isFunctor:TermF {σ}) f = incl ′ map-Term ⟨ f ⟩ ′
  isFunctor.isSetoidHom:map isFunctor:TermF = {!!}
  isFunctor.functoriality-id isFunctor:TermF = {!!}
  isFunctor.functoriality-◆ isFunctor:TermF = {!!}






