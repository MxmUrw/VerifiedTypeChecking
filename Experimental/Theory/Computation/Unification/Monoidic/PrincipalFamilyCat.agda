
module Verification.Experimental.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Category.Std.Category.As.Monoid
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Theory.Computation.Unification.Definition
open import Verification.Experimental.Theory.Computation.Unification.Monoidic.PrincipalFamily
open import Verification.Experimental.Theory.Presentation.Signature.Definition

module _ {M : 𝒰 𝑖} {{_ : Monoid₀ (𝑖 , 𝑖) on M}} where

  record CoeqSolutions' (f g h : M) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : f ⋆ h ∼ g ⋆ h
  open CoeqSolutions' public

  CoeqSolutions : (f g : M) -> 𝒫 M
  CoeqSolutions f g = λ h -> ∣ CoeqSolutions' f g h ∣

module _ {M : Monoid₀ (𝑖 , 𝑖)} {f g : ⟨ M ⟩} where
  instance
    isSubsetoid:CoeqSolutions : isSubsetoid (CoeqSolutions f g)
    isSubsetoid.transp-Subsetoid isSubsetoid:CoeqSolutions (p) (incl P) = incl ((refl ≀⋆≀ p ⁻¹) ∙ P ∙ (refl ≀⋆≀ p))

  instance
    isIdeal-r:CoeqSolutions : isIdeal-r M ′(CoeqSolutions f g)′
    isIdeal-r.ideal-r-⋆ isIdeal-r:CoeqSolutions {h} (incl P) i =
      let P₀ : f ⋆ (h ⋆ i) ∼ g ⋆ (h ⋆ i)
          P₀ = f ⋆ (h ⋆ i)   ⟨ assoc-r-⋆ ⟩-∼
                (f ⋆ h) ⋆ i   ⟨ P ≀⋆≀ refl ⟩-∼
                (g ⋆ h) ⋆ i   ⟨ assoc-l-⋆ ⟩-∼
                g ⋆ (h ⋆ i)   ∎
      in incl P₀
    isIdeal-r.ideal-◍ isIdeal-r:CoeqSolutions = incl (absorb-r-⋆ ∙ absorb-r-⋆ ⁻¹)


record PrincipalFamilyCat (𝒞 : Category 𝑖) (a : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ⁺) where
  field SizeC : 𝒰₀
  field isBase : ∀(x) -> (h : a ⟶ x) -> 𝒰 (𝑖 ⌄ 1)
  field sizeC : ⟨ 𝒞 ⟩ -> SizeC
  field _<<C_ : SizeC -> SizeC -> 𝒰₀
  field trans-SizeC : ∀{a b c} -> a <<C b -> b <<C c -> a <<C c
  field isWellFounded:SizeC : WellFounded _<<C_
  _≤C_ : SizeC -> SizeC -> 𝒰₀
  a ≤C b = (a ≡-Str b) ∨ (a <<C b)
  field size0 : SizeC
  field initial-size0 : ∀{a} -> size0 ≤C a

open PrincipalFamilyCat {{...}} public

data Side : 𝒰₀ where
  isLeft isRight : Side

module _ (𝒞 : Category 𝑖) {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} (a : ⟨ 𝒞 ⟩) {{F : PrincipalFamilyCat 𝒞 a}} where
  private
    Ix = Maybe (∑ λ (x : ⟨ 𝒞 ⟩) -> Hom a x ∧ Hom a x)
    Bx = Maybe (∑ λ (x : ⟨ 𝒞 ⟩) -> Side ×-𝒰 ((∑ isBase x) ∧ Hom a x))

    size' : Ix -> SizeC
    size' nothing = size0
    size' (just (x , _)) = sizeC x

    bb : Bx -> Ix
    bb nothing = nothing
    bb (just (x , isLeft , ((h , _) , f)))  = just (x , h , f)
    bb (just (x , isRight , ((h , _) , f))) = just (x , f , h)


    M : Monoid₀ _
    M = ′ PathMon 𝒞 ′

    𝓘 : Ix -> Ideal-r M
    𝓘 nothing = ⊤
    𝓘 (just (_ , f , g)) = ′(CoeqSolutions (arrow f) (arrow g))′

    Good : 𝒫 (PathMon 𝒞)
    Good [] = ⊤
    Good idp = ⊤
    Good (arrow {x} {y} f) = ∣ Lift (sizeC y <<C sizeC x) ∣

    _⁻¹'_ : ⦋ Good ⦌ -> Ix -> Ix
    _⁻¹'_ (a) nothing = nothing
    _⁻¹'_ ([] ∢ _) (just _) = nothing
    _⁻¹'_ (idp ∢ _) (just (x , (f , g))) = just (x , (f , g))
    _⁻¹'_ (arrow {a} {b} h ∢ _) (just (x , (f , g))) with (x ≟-Str a)
    ... | yes refl-StrId = just (b , (f ◆ h , g ◆ h))
    ... | no ¬p = nothing

    lem-10 : (g : ⦋ Good ⦌) (i : Ix) → (size' (g ⁻¹' i) ≤C size' i)
    lem-10 (g ∢ gp) nothing = left refl
    lem-10 ([] ∢ hp) (just (x , (f , g))) = initial-size0
    lem-10 (idp ∢ hp) (just (x , (f , g))) = left refl
    lem-10 (arrow {a} {b} h ∢ (↥ hp)) (just (x , (f , g))) with (x ≟-Str a)
    ... | no ¬p = initial-size0
    ... | yes refl-StrId = right hp

    lem-20 : {g : ⦋ Good ⦌} {i : Ix} → 𝓘 (g ⁻¹' i) ∼ (⟨ g ⟩ ⁻¹↷-Ide 𝓘 i)
    lem-20 {g ∢ gp} {nothing} = unit-r-⁻¹↷-Ide ⁻¹
    lem-20 {[] ∢ gp} {just (x , (f , g))} = absorb-l-⁻¹↷-Ide ⁻¹
    lem-20 {idp ∢ gp} {just (x , (f , g))} = unit-l-⁻¹↷-Ide ⁻¹
    lem-20 {arrow {a} {b} h ∢ gp} {just (x , (f , g))} with (x ≟-Str a)
    ... | no ¬p =
      let P₀ : ⊤ ≤ ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′)
          P₀ = incl (λ {a} x₁ → incl (incl (
                    arrow f ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow f} {b = arrow h} ⟩-∼
                    (arrow f ⋆ arrow h) ⋆ a    ⟨ PathMon-non-matching-arrows ¬p f h ≀⋆≀ refl ⟩-∼
                    [] ⋆ a                     ⟨ PathMon-non-matching-arrows ¬p g h ⁻¹ ≀⋆≀ refl ⟩-∼
                    (arrow g ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow g} {b = arrow h} ⟩-∼
                    arrow g ⋆ (arrow h ⋆ a)    ∎
               )))
      in antisym P₀ terminal-⊤
    ... | yes refl-StrId =
      let P₀ : ′(CoeqSolutions (arrow (f ◆ h)) (arrow (g ◆ h)))′ ≤ ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′)
          P₀ = incl (λ {a} (incl P) → incl (incl (
                    arrow f ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow f} {b = arrow h} ⟩-∼
                    (arrow f ⋆ arrow h) ⋆ a    ⟨ functoriality-arrow f h ⁻¹ ≀⋆≀ refl ⟩-∼
                    (arrow (f ◆ h)) ⋆ a        ⟨ P ⟩-∼
                    (arrow (g ◆ h)) ⋆ a        ⟨ functoriality-arrow g h ≀⋆≀ refl ⟩-∼
                    (arrow g ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow g} {b = arrow h} ⟩-∼
                    arrow g ⋆ (arrow h ⋆ a)    ∎
               )))
          P₁ : ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′) ≤ ′(CoeqSolutions (arrow (f ◆ h)) (arrow (g ◆ h)))′
          P₁ = incl (λ {a} (incl (incl P)) → incl (
                    (arrow (f ◆ h)) ⋆ a        ⟨ functoriality-arrow f h ≀⋆≀ refl ⟩-∼
                    (arrow f ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow f} {b = arrow h} ⟩-∼
                    arrow f ⋆ (arrow h ⋆ a)    ⟨ P ⟩-∼
                    arrow g ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow g} {b = arrow h} ⟩-∼
                    (arrow g ⋆ arrow h) ⋆ a    ⟨ functoriality-arrow g h ⁻¹ ≀⋆≀ refl ⟩-∼
                    (arrow (g ◆ h)) ⋆ a        ∎
               ))
      in antisym P₀ P₁

    instance
      isSubsetoid:Good : isSubsetoid Good
      isSubsetoid.transp-Subsetoid isSubsetoid:Good (incl idp) P = tt
      isSubsetoid.transp-Subsetoid isSubsetoid:Good (incl []) P = P
      isSubsetoid.transp-Subsetoid isSubsetoid:Good (incl (arrow f∼g)) (↥ p) = ↥ p

      isSubmonoid:Good : isSubmonoid ′ Good ′
      isSubmonoid.closed-◌ isSubmonoid:Good = tt
      isSubmonoid.closed-⋆ isSubmonoid:Good {idp} {b} p1 p2 = p2
      isSubmonoid.closed-⋆ isSubmonoid:Good {[]} {b} p1 p2 = p1
      isSubmonoid.closed-⋆ isSubmonoid:Good {arrow f} {[]} p1 p2 = p2
      isSubmonoid.closed-⋆ isSubmonoid:Good {arrow f} {idp} p1 p2 = p1
      isSubmonoid.closed-⋆ isSubmonoid:Good {arrow {a} {b} f} {arrow {c} {d} g} (↥ p1) (↥ p2) with (b ≟-Str c)
      ... | yes refl-StrId = ↥ (trans-SizeC p2 p1)
      ... | no ¬p = tt
      -- record
      --   { closed-◌ = tt
      --   ; closed-⋆ = λ p1 p2 -> ?
      --   }

    lem-50 : isPrincipalFamily M ′ Good ′ bb 𝓘
    lem-50 = record
               { Size = SizeC
               ; size = size'
               ; _<<_ = _<<C_
               ; isWellFounded:Size = isWellFounded:SizeC
               ; trans-Size = trans-SizeC
               ; _⁻¹*_ = _⁻¹'_
               ; size:⁻¹* = lem-10
               ; preserves-𝓘:⁻¹* = λ {g} {i} -> lem-20 {g} {i}
               ; ∂ = {!!}
               ; principalBase = {!!}
               }

  -- module _ {B I : 𝒰₀} (𝒷 : B -> I) (𝓘 : I -> Ideal-r M) where

      -- field size : I -> Size
      -- field _<<_ : Size -> Size -> 𝒰₀
      -- field isWellFounded:Size : WellFounded _<<_
      -- field trans-Size : ∀{a b c} -> a << b -> b << c -> a << c
      -- field _⁻¹*_ : ⦋ ⟨ Good ⟩ ⦌ -> I -> I
      -- field size:⁻¹* : ∀ g i -> (size (g ⁻¹* i) ≡-Str size i) +-𝒰 (size (g ⁻¹* i) << size i)
      -- field preserves-𝓘:⁻¹* : ∀ {g i} -> 𝓘 (g ⁻¹* i) ∼ (⟨ g ⟩ ⁻¹↷-Ide (𝓘 i))
      -- -- field 𝓘 : Idx -> Ideal-r M
      -- field ∂ : (i : I) -> (∑ λ b -> 𝒷 b ≡-Str i) +-𝒰 (∑ λ n -> isSplittable n i (λ j -> size j << size i))
      -- field principalBase : ∀ b -> isPrincipal/⁺-r Good (𝓘 (𝒷 b))
