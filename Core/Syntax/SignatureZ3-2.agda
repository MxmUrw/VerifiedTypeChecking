
module Verification.Core.Syntax.SignatureZ3-2 where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Type
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Limit.Kan
open import Verification.Core.Syntax.SignatureZ3
-- open import Verification.Unification.RecAccessible


module _ {K : 𝒰₀} where
  module _ {σ : Signature} {V : K -> 𝒰₀} where

    reduce-forget-Term : ∀{k} -> (t : Termᵥ σ V k) -> ∑ λ x -> reduce-Term (forget-Term t) ≡-Str right x
    reduce-forget-Term t = {!!}

    reduce-forget-Terms : ∀{ks : Vec K n} -> (ts : Termsᵥ σ V ks) -> ∑ λ x -> reduce-Terms (forget-Terms ts) ≡-Str right x
    reduce-forget-Terms (x ∷ ts) with reduce-Term (forget-Term x) | reduce-forget-Term x
    ... | just x₁ | Y = _ , refl
    reduce-forget-Terms (fail∷_ {k = k} ts) = ?
    -- with (fail {σ = σ} {V = V} {k = k})
    -- ... | X  = {!!}

    join-te-forget : ∀{ks : Vec K (suc n)} -> ∀{k} -> (s : σ k ks)-> (ts : Termsᵥ σ V ks) -> join-te s (forget-Terms ts) ≡ te s ts
    join-te-forget s ts with split-+-Str (reduce-Terms (forget-Terms ts))
    ... | left x = {!!}
    ... | just ((x , xP) , xQ) with isInjective:forget-Terms (≡→≡-Str xP)
    ... | refl-StrId = refl

    unit-r-join-Term : ∀{k} -> (x : Term σ V k) -> join-Term (map-Term var x) ≡ x
    unit-r-join-Terms : ∀{ks : Vec K n} -> (ts : Terms σ V ks) -> join-Terms (map-Terms var ts) ≡ ts
    unit-r-join-Termᵥ : ∀{k} -> (x : Termᵥ σ V k) -> join-Termᵥ (map-Termᵥ var x) ≡ forget-Term x

    unit-r-join-Termsᵥ : ∀{ks : Vec K n} -> (ts : Termsᵥ σ V ks) -> join-Termsᵥ (map-Termsᵥ var ts) ≡ forget-Terms ts
    unit-r-join-Termsᵥ (x ∷ ts) i = unit-r-join-Termᵥ x i ∷ unit-r-join-Terms ts i
    unit-r-join-Termsᵥ (fail∷ ts) i = fail ∷ unit-r-join-Termsᵥ ts i

    unit-r-join-Terms [] = refl
    unit-r-join-Terms (t ∷ ts) i = unit-r-join-Term t i ∷ unit-r-join-Terms ts i

    unit-r-join-Termᵥ (te s ts) = join-te s (join-Termsᵥ (map-Termsᵥ var ts)) ≡[ i ]⟨ join-te s (unit-r-join-Termsᵥ ts i) ⟩
                                  join-te s (forget-Terms ts)                 ≡⟨ join-te-forget s ts ⟩
                                  te s ts                                     ∎
    unit-r-join-Termᵥ (var x) = refl

    unit-r-join-Term (te s ts) = {!!}
    unit-r-join-Term (var x) = refl
    unit-r-join-Term fail = refl
