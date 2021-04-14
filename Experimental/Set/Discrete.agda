
module Verification.Experimental.Set.Discrete where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure

record isDiscrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field _≟-Str_ : (a b : A) -> Decision (a ≡-Str b)
open isDiscrete {{...}} public


