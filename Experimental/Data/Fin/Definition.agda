
module Verification.Experimental.Data.Fin.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Prop.Subset
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
-- open import Verification.Experimental.Set.Finite.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Totalorder


module _ {n : ℕ} where
  instance
    isSetoid:Fin : isSetoid _ (Fin n)
    isSetoid._∼'_ (isSetoid:Fin) = _≡_
    isSetoid.isEquivRel:∼ (isSetoid:Fin) = it

  instance
    isPreorder:Fin : isPreorder _ ′(Fin n)′
    isPreorder._≤'_ isPreorder:Fin (i , _) (j , _) = i ≤-ℕ j
    isPreorder.reflexive isPreorder:Fin = incl (0 , refl)
    isPreorder._⟡_ isPreorder:Fin = {!!}
    isPreorder.transp-≤ isPreorder:Fin = {!!}

  instance
    isPartialorder:Fin : isPartialorder ′(Fin n)′
    isPartialorder.antisym isPartialorder:Fin = {!!}

  instance
    isTotalorder⁺:Fin : isTotalorder⁺ ′(Fin n)′
    isTotalorder⁺.total⁺ isTotalorder⁺:Fin = {!!}

  instance
    isDiscrete':Fin : isDiscrete' (Fin n)
    is𝒫-Dec.decide-𝒫 (isDiscrete'.decidableEquality isDiscrete':Fin) = {!!}

  -- instance
  --   isFinite:Fin : isFinite ′(Fin n)′
  --   isFinite:Fin = {!!}


