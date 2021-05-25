
module Verification.Experimental.Theory.Computation.Problem.Specific.Forall where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Computation.Problem.Definition


record ForallProblem (𝑖 : 𝔏 ^ 2) : 𝒰 (𝑖 ⁺) where
  constructor forallP
  field Base : 𝒰 (𝑖 ⌄ 0)
  field Statement : Base -> 𝒰 (𝑖 ⌄ 1)

open ForallProblem public

ForallSolution : (ForallProblem 𝑖) -> 𝒰 _
ForallSolution P = ∀ a -> P .Statement a

macro
  FORALL : ∀ 𝑖 -> SomeStructure
  FORALL 𝑖 = #structureOn (ForallProblem 𝑖)

instance
  isProblem:FORALL : isProblem _ (FORALL 𝑖)
  isProblem:FORALL = problem (ForallSolution)



