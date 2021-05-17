
module Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Definition where

open import Verification.Conventions


Signature : 𝒰 _
Signature = ℕ -> 𝒰₀


module _ where

  data Term (s : Signature) (V : 𝒰 𝑖) : 𝒰 𝑖
  data Terms (σ : Signature) (V : 𝒰 𝑖) : ℕ -> 𝒰 𝑖 where
    [] : Terms σ V 0
    _∷_ : Term σ V -> Terms σ V n -> Terms σ V (suc n)

  data Term σ V where
    te : ∀{n} -> σ n -> Terms σ V n -> Term σ V
    var : V -> Term σ V





