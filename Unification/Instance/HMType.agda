
module Verification.Unification.Instance.HMType where

open import Verification.Conventions
open import Verification.Unification.Instance.Signature


data Type : 𝒰₀ where
  _⇒_ : Type -> Type -> Type
  𝐵 : Type
  𝑁 : Type
  var : Fin n -> Type
  □ : Type

K = 𝟙-𝒰

V = λ (_ : 𝟙-𝒰) -> 𝟘-𝒰

data σ : K -> Vec K n -> 𝒰₀ where
  `⇒` : σ tt (tt ∷ tt ∷ [])
  `𝐵` : σ tt []
  `𝑁` : σ tt []

ϕ : Term σ V tt -> Type
ϕ (te `⇒` (x ∷ (y ∷ []))) = ϕ x ⇒ ϕ y
ϕ (te `𝐵` []) = 𝐵
ϕ (te `𝑁` []) = 𝑁

-- ψ : Type -> Term σ V tt
-- ψ (t ⇒ s) = (te `⇒` (ψ t ∷ (ψ s ∷ [])))
-- ψ 𝐵 = (te `𝐵` [])
-- ψ 𝑁 = (te `𝑁` [])














