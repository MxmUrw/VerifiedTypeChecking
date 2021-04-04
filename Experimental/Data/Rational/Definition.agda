
module Verification.Experimental.Data.Rational.Definition where

open import Verification.Conventions
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Algebra.Ring.Localization

private
  NZ : 𝒫 ℤ
  NZ a = ∑ λ b -> a ≡-Str (pos (suc b))

  instance
    isSubsetoid:NZ : isSubsetoid NZ
    isSubsetoid.transp-Subsetoid isSubsetoid:NZ (incl p) (b , refl-StrId) = {!!} , {!!}

  instance
    isMCS:NZ : isMCS ′ ℤ ′ ′ NZ ′
    isMCS.closed-⋅ isMCS:NZ = {!!}
    isMCS.closed-⨡ isMCS:NZ = {!!}

ℚ = Localize ′ ℤ ′ ′ NZ ′

-- ta tb : ℚ
-- ta = pos 1 / (pos 2 ∈ (1 , it))

-- tb = negsuc 23 / (pos 3 ∈ (2 , it))

-- tc = ta ⋆ tb


