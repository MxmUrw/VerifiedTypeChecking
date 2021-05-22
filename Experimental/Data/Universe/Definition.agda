
module Verification.Experimental.Data.Universe.Definition where

open import Verification.Experimental.Conventions

-- | - The identity morphisms [..] are given by [..].
id-𝒰 : ∀{A : 𝒰 𝑖} -> A -> A
id-𝒰 a = a

-- | - Let [..], [..] and [..] be types.
module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
-- |> Then composition is given by:
  _◆-𝒰_ : (f : A -> B) -> (g : B -> C) -> (A -> C)
  _◆-𝒰_ f g a = g (f a)
  infixl 40 _◆-𝒰_


𝐓𝐲𝐩𝐞 : ∀(𝑖) -> SomeStructure
𝐓𝐲𝐩𝐞 (𝑖) = structureOn (𝒰 𝑖)


_↔_ : ∀{𝑖 𝑗} -> 𝒰 𝑖 -> 𝒰 𝑗 -> 𝒰 _
A ↔ B = (A -> B) ×-𝒰 (B -> A)


