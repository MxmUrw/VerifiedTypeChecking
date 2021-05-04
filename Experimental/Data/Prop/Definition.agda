
module Verification.Experimental.Data.Prop.Definition where

open import Verification.Conventions

record Prop (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  constructor ∣_∣-Prop
  field ⟨_⟩ : 𝒰 𝑖
open Prop public

instance
  Notation-Absolute:Prop : Notation-Absolute (𝒰 𝑖) (Prop 𝑖)
  Notation-Absolute.∣_∣ Notation-Absolute:Prop = ∣_∣-Prop


𝒫 : 𝒰 𝑖 -> 𝒰 (𝑖 ⁺)
𝒫 {𝑖} A = A -> Prop 𝑖

record ⦋_⦌ {U : 𝒰 𝑖} (P : U -> Prop 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  constructor _∈_
  field ⟨_⟩ : U
  field Proof : Prop.⟨_⟩ (P ⟨_⟩)
open ⦋_⦌ public

infix 60 _∈_



