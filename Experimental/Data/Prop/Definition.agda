
module Verification.Experimental.Data.Prop.Definition where

open import Verification.Conventions

record Prop (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  constructor ∣_∣-Prop
  field ⟨_⟩ : 𝒰 𝑖
open Prop public

instance
  Notation-Absolute:Prop : Notation-Absolute (𝒰 𝑖) (Prop 𝑖)
  Notation-Absolute.∣_∣ Notation-Absolute:Prop = ∣_∣-Prop


