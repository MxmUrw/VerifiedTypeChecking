
module Verification.Experimental.Theory.Computation.Problem.Specific.Coequalizer where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Theory.Computation.Problem.Definition
open import Verification.Experimental.Theory.Computation.Problem.Specific.Forall
-- open import Verification.Experimental.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat
-- open import Verification.Experimental.Theory.Computation.Refinement.Paradigm.DivideAndConquer

record UnificationProblem (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  constructor unifyP
  field 𝒞 : Category 𝑖
  field {{isDiscrete:𝒞}} : isDiscrete ⟨ 𝒞 ⟩
  field {{isSet-Str:𝒞}} : isSet-Str ⟨ 𝒞 ⟩
  -- field a b : ⟨ 𝒞 ⟩
  -- field f g : a ⟶ b

macro
  UNIFY : ∀ 𝑖 -> SomeStructure
  UNIFY 𝑖 = #structureOn (UnificationProblem 𝑖)

-- UNIFY = UnificationProblem

module _ {𝒞 : Category 𝑖} where
  record Pair : 𝒰 𝑖 where
    constructor pair
    field {PairDomain} : ⟨ 𝒞 ⟩
    field {PairCodomain} : ⟨ 𝒞 ⟩
    field arrow₀ arrow₁ : PairDomain ⟶ PairCodomain

  hasUnification : Pair -> 𝒰 _
  hasUnification (pair f g) = isDecidable (∑ isCoequalizer f g)

instance
  isProblem:UNIFY : ∀{𝑖 : 𝔏 ^ 3} -> isProblem _ (UNIFY 𝑖)
  isProblem:UNIFY = problem (λ P -> ∀ (a : Pair {𝒞 = UnificationProblem.𝒞 P}) -> hasUnification a)




-- instance
--   isProblem:COEQ : isProblem (⨆ 𝑖) (COEQ 𝑖)
--   isProblem:COEQ = record
--     { Solution = λ a → ∑ (λ (x : ⟨ CoeqProblem.𝒞 a ⟩) -> isCoequalizer (CoeqProblem.f a) (CoeqProblem.g a) x)
--     }

{-
record EpiPrincipalProblem (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  field M : Monoid₀ (𝑖 , 𝑖)
  field Ideal : Ideal-r M

EPIPRI : ∀ 𝑖 -> SomeStructure
EPIPRI 𝑖 = structureOn (EpiPrincipalProblem 𝑖)


instance
  isProblem:EPIPRI : isProblem (𝑖 , 𝑖) (EPIPRI 𝑖)
  isProblem:EPIPRI = record
    { Property = const ⊤-𝒰
    ; Solution = λ P a _ -> isEpiPrincipal (EpiPrincipalProblem.Ideal a)
    }


reduceCoeq : COEQ 𝑖 -> EPIPRI _
reduceCoeq π = record
  { M = 𝖯𝖺𝗍𝗁𝖬𝗈𝗇 (CoeqProblem.𝒞 π)
  ; Ideal = ′ CoeqSolutions (arrow (CoeqProblem.f π)) (arrow (CoeqProblem.g π)) ′
  }

instance
  isReduction:reduce-Coeq : isReduction (COEQ 𝑖) (EPIPRI _) reduceCoeq
  isReduction:reduce-Coeq = record { propMap = λ P x → tt ; solutionMap = λ P PX a pa → {!!} }


coeq-epipri : ∀ 𝑖 -> SomeStructure
coeq-epipri 𝑖 = structureOn (reduceCoeq {𝑖 = 𝑖})


ff : COEQ (𝑖 , 𝑖 , 𝑖) ⟶ EPIPRI _
ff = incl (coeq-epipri _)

xxx : 分 (EPIPRI 𝑖) ⟶ EPIPRI 𝑖
xxx = ε-分


-}
