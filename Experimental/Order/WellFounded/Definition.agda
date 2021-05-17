
module Verification.Experimental.Order.WellFounded.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Experimental.Meta.Structure


record isWF 𝑗 (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
  field _≪_ : A -> A -> 𝒰 𝑗
  field wellFounded : WellFounded _≪_
open isWF {{...}} public

WF : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
WF 𝑖 = (𝒰 (𝑖 ⌄ 0)) :& isWF (𝑖 ⌄ 1)

module _ {A : 𝒰 𝑖} {{_ : isWF 𝑗 A}} where
  _⪣_ : A -> A -> 𝒰 _
  _⪣_ a b = (a ≡-Str b) +-𝒰 (a ≪ b)

record isWFT (A : WF 𝑖) : 𝒰 (𝑖) where
  field _⟡-≪_ : ∀{a b c : ⟨ A ⟩} -> a ≪ b -> b ≪ c -> a ≪ c

open isWFT {{...}} public

WFT : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
WFT 𝑖 = (WF 𝑖) :& isWFT




