
module Verification.Experimental.Algebra.Ring.Localization.Instance.Group where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Setoid
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Monoid


module _ {R : CRing 𝑖} {M : MCS R} where

  instance
    isGroup:Localize : isGroup ′ Localize R M ′
    isGroup.◡ isGroup:Localize = ?
    isGroup.inv-l-⋆ isGroup:Localize = ?
    isGroup.inv-r-⋆ isGroup:Localize = ?
    isGroup.cong-◡ isGroup:Localize = ?



