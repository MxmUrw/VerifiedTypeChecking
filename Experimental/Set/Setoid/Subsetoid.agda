
module Verification.Experimental.Set.Setoid.Subsetoid where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice

module _ {X : Setoid 𝑖} where

  instance
    isSetoid:Subsetoid : isSetoid _ (Subsetoid X)
    isSetoid:Subsetoid = isSetoid:hasU

  instance
    isPreorder:Subsetoid : isPreorder _ ′(Subsetoid X)′
    isPreorder._≤'_ isPreorder:Subsetoid a b = ⟨ a ⟩ ≤' ⟨ b ⟩
    isPreorder.reflexive isPreorder:Subsetoid = incl ⟨ reflexive ⟩
    isPreorder._⟡_ isPreorder:Subsetoid p q = incl ⟨ incl ⟨ p ⟩ ⟡ incl ⟨ q ⟩ ⟩
    isPreorder.transp-≤ isPreorder:Subsetoid p q P = {!!}

  instance
    isSubsetoid:⊤ : isSubsetoid {A = ⟨ X ⟩} ⊤
    isSubsetoid.transp-Subsetoid isSubsetoid:⊤ p _ = tt

  instance
    hasFiniteMeets:Subsetoid : hasFiniteMeets ′(Subsetoid X)′
    hasFiniteMeets.⊤ hasFiniteMeets:Subsetoid = ′ ⊤ ′
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Subsetoid = {!!}
    hasFiniteMeets._∧_ hasFiniteMeets:Subsetoid = {!!}
    hasFiniteMeets.π₀-∧ hasFiniteMeets:Subsetoid = {!!}
    hasFiniteMeets.π₁-∧ hasFiniteMeets:Subsetoid = {!!}
    hasFiniteMeets.⟨_,_⟩-∧ hasFiniteMeets:Subsetoid = {!!}


