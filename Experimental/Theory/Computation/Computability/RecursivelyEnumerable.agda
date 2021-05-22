
module Verification.Experimental.Theory.Computation.Computability.RecursivelyEnumerable where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition


data Bar {A : 𝒰 𝑖} (P : List A -> 𝒰 𝑗) : List A -> 𝒰 (𝑖 ､ 𝑗) where
  Done : ∀{as : List A} -> P as -> Bar P as
  Next : ∀{as : List A} -> (∀(a : A) -> Bar P (a ∷ as)) -> Bar P as


