
module Verification.Experimental.Set.Discrete where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Data.Prop.Everything

record isDiscrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field _≟-Str_ : (a b : A) -> Decision (a ≡-Str b)
open isDiscrete {{...}} public

record isDiscrete' (A : 𝒰 𝑖) : 𝒰 (𝑖) where
  field {{decidableEquality}} : ∀{a : A} -> is𝒫-Dec (λ b -> ∣ a ≡-Str b ∣)
open isDiscrete' {{...}} public

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  instance
    isDiscrete':+ : {{_ : isDiscrete' A}} {{_ : isDiscrete' B}} -> isDiscrete' (A +-𝒰 B)
    isDiscrete'.decidableEquality isDiscrete':+ = {!!}

