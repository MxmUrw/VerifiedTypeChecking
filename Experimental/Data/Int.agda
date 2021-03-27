
module Verification.Experimental.Data.Int where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Monoid

instance
  isSetoid:ℤ : isSetoid _ ℤ
  isSetoid._∼_ isSetoid:ℤ = _≡_
  isSetoid.IEquiv:∼ isSetoid:ℤ = it

instance
  isMonoid:ℤ : isMonoid ′ ℤ ′
  isMonoid._⋆_ isMonoid:ℤ = _+-ℤ_
  isMonoid.◌ isMonoid:ℤ = pos 0
  isMonoid.unit-l-⋆ isMonoid:ℤ = pos0+ _ ⁻¹
  isMonoid.unit-r-⋆ isMonoid:ℤ = refl
  isMonoid.assoc-l-⋆ isMonoid:ℤ {a} {b} {c} = assoc-+-ℤ a b c ⁻¹
  isMonoid.assoc-r-⋆ isMonoid:ℤ {a} {b} {c} = assoc-+-ℤ a b c
  isMonoid._`cong-⋆`_ isMonoid:ℤ p q = λ i -> p i +-ℤ q i

  isCommutative:ℤ : isCommutative ′ ℤ ′
  isCommutative.comm-⋆ isCommutative:ℤ {a} {b} = comm-+-ℤ a b

instance
  isGroup:ℤ : isGroup ′ ℤ ′
  isGroup.◡_ isGroup:ℤ a = 0 -ℤ a
  isGroup.inv-l-⋆ isGroup:ℤ {a} = minusPlus a (pos 0)
  isGroup.inv-r-⋆ isGroup:ℤ {a} = comm-⋆ {a = a} ∙ (minusPlus a (pos 0))
  isGroup.cong-◡_ isGroup:ℤ p = λ i -> pos 0 -ℤ p i

open import Cubical.Data.Bool renaming (_⊕_ to _⊕-Bool_)

fromSign : Bool -> ℕ -> ℤ
fromSign false zero = pos 0
fromSign false (suc n) = negsuc n
fromSign true n = pos n

_⋅-ℤ_ : ℤ -> ℤ -> ℤ
a ⋅-ℤ b = fromSign (sgn a ⊕-Bool sgn b) (abs a *-ℕ abs b)

instance
  isSemiring:ℤ : isSemiring ′ ℤ ′
  isSemiring._⋅_ isSemiring:ℤ = _⋅-ℤ_
  isSemiring.⨡ isSemiring:ℤ = pos 1
  isSemiring.unit-l-⋅ isSemiring:ℤ = {!!}
  isSemiring.unit-r-⋅ isSemiring:ℤ = {!!}
  isSemiring.assoc-l-⋅ isSemiring:ℤ = {!!}
  isSemiring.distr-l-⋅ isSemiring:ℤ = {!!}
  isSemiring.distr-r-⋅ isSemiring:ℤ = {!!}
