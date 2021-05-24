
module Verification.Experimental.Theory.Computation.Problem.Paradigm.DivideAndConquer where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Theory.Computation.Problem.Definition
-- open import Verification.Experimental.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat


---------------------------------------------------------------
-- Every problem can be turned into the problem of
-- finding a divide and conquer solution

record DivideAndConquer (Π : Problem 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  field original : ⟨ Π ⟩
open DivideAndConquer {{...}} public

record DivideAndConquerProp (Π : Problem 𝑖) (P : DivideAndConquer Π -> 𝒰 _) : 𝒰 (fst 𝑖 ､ (fst (snd 𝑖)) ⁺) where
  field Size : WFT (ℓ₀ , ℓ₀)
  field size : (∑ P) -> ⟨ Size ⟩
  field originalP : Property {{of Π}} (λ x -> (P (record {original = x})))
  -- field ∂ : ⟨ Π ⟩ -> ∑ λ n -> Fin-R n -> ⟨ Π ⟩
  -- field size-∂ : ∀ p -> ∀ i -> size (∂ p .snd i) ≪ size p

open DivideAndConquerProp {{...}} public

DAC : ∀ (Π : Problem 𝑖) -> SomeStructure
DAC Π = structureOn (DivideAndConquer Π)

instance
  isProblem:DAC : ∀{Π : Problem 𝑖} -> isProblem ((𝑖 ⌄ 1) , 𝑖 ⌄ 2) (DAC Π)
  isProblem:DAC {Π = Π} = record
    { Property = DivideAndConquerProp Π
    ; Solution = {!!}
    }

ぶん : Problem 𝑖 -> Problem 𝑖
ぶん Π = DAC Π

分 : ∀ {𝑖} -> SomeStructure
分 {𝑖} = structureOn (ぶん {𝑖})

private
  module _ {Π : Problem 𝑖} where
    ε : DAC Π -> ⟨ Π ⟩
    ε x = x .original

    instance
      isReduction:ε : isReduction (DAC Π) Π ε
      isReduction:ε = record
        { propMap = λ P x → let y = originalP {{x}}
                            in {!!}
        ; solutionMap = {!!}
        }

ε-分 : ∀{Π : Problem 𝑖} -> 分 Π ⟶ Π
ε-分 = incl ′ ε ′


{-
-- record DivideAndConquerSolution {Π : Problem 𝑖} (P : DivideAndConquer Π) : 𝒰 𝑖 where
--   field ∂-solves : ∀ (p : ⟨ Π ⟩) -> (∀ i -> SolutionSpace (∂ {{P}} p .snd i)) -> SolutionSpace p


module _ {Π : Problem 𝑖} where
  instance
    isProblem:DAC : isProblem (𝑖 ⌄ 1) (DAC Π)
    isProblem:DAC = record
      { Property = DivideAndConquerProp Π
      ; Solution = {!!}
      }
    -- record { SolutionSpace = DivideAndConquerSolution }

dac : Problem 𝑖 -> Problem _
dac Π = DAC Π

fmap-dac : ∀{Ω Π : Problem 𝑖} -> (f : Reduction Ω Π) -> DAC Ω -> DAC Π
fmap-dac f x = record { original = ⟨ f ⟩ (x .original) }

instance
  isReduction:fmap-dac : ∀{Ω Π : Problem 𝑖} -> {f : Reduction Ω Π} -> isReduction (DAC Ω) (DAC Π) (fmap-dac f)
  isReduction:fmap-dac {f = f} = record
    { propMap = λ P x → record
                        { Size = x .Size
                        ; size = λ (a , b , c) → let Q = x .size
                                                 in Q (_ , c .fst )
                        ; originalP = let Q = x .originalP
                                          xx = propMap {{of f}} _ Q
                                      in {!!}
                        }
    ; solutionMap = {!!}
                         -- { Size = x .Size
                         -- ; size = λ y → let f = x .size
                         --                in f (_ , y .snd)
                         -- ; originalP = let Q = x .originalP
                         --                   xx = propMap {{of f}} _ Q
                         --               in xx
                         -- }
    }

module _ {Π : Problem 𝑖} where
  -- η-DAC : ⟨ Π ⟩ -> DAC Π
  -- η-DAC x = record { original = x }

  η-DAC : DAC Π -> ⟨ Π ⟩
  η-DAC x = x .original

  instance
    isReduction:η-DAC : isReduction (DAC Π) Π η-DAC
    isReduction:η-DAC = record
      { propMap = λ P x → let y = originalP {{x}}
                          in {!!}
      ; solutionMap = {!!}
      }


-}
