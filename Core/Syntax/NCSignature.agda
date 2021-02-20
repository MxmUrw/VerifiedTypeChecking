
module Verification.Core.Syntax.NCSignature where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
-- open import Verification.Unification.RecAccessible

module _ {K : 𝒰₀} where
  -- Symbol : 𝒰₀
  -- Symbol = ∑ λ (n : ℕ) -> K ×-𝒰 (Vec K n)

  Signature : 𝒰₁
  Signature = {n : ℕ} -> K -> Vec K (suc n) -> 𝒰₀

  data Term (s : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀
  data Terms (σ : Signature) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀ where
    [] : Terms σ V []
    _∷_ : ∀{k} {ks : Vec K n} -> Term σ V k -> Terms σ V ks -> Terms σ V (k ∷ ks)

  data Term σ V k where
    te : ∀{ks : Vec K (suc n)} -> σ k ks -> Terms σ V ks -> Term σ V k
    var : V k -> Term σ V k

  private
    𝒞 : Category _
    𝒞 = Category:IdxSet K ℓ₀

  module _ (σ : Signature) where
    Functor:Term : Functor 𝒞 𝒞
    ⟨ ⟨ Functor:Term ⟩ X ⟩ = Term σ ⟨ X ⟩
    IIdxSet.ISet:this (of ⟨ Functor:Term ⟩ z) = {!!}
    IFunctor.map (of Functor:Term) = {!!}
    IFunctor.functoriality-id (of Functor:Term) = {!!}
    IFunctor.functoriality-◆ (of Functor:Term) = {!!}
    IFunctor.functoriality-≣ (of Functor:Term) = {!!}

    Monad:Term : Monad 𝒞
    ⟨ Monad:Term ⟩ = Functor:Term
    IMonad.return (of Monad:Term) = {!!}
    IMonad.join (of Monad:Term) = {!!}
    IMonad.INatural:return (of Monad:Term) = {!!}
    IMonad.INatural:join (of Monad:Term) = {!!}
    IMonad.unit-l-join (of Monad:Term) = {!!}
    IMonad.unit-r-join (of Monad:Term) = {!!}
    IMonad.assoc-join (of Monad:Term) = {!!}





