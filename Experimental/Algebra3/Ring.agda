
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra.Ring where

open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Quotient



-- open import Verification.Conventions
-- -- open import Verification.Core.Category.Definition

-- open import Verification.Experimental.Meta.Structure
-- open import Verification.Experimental.Algebra.Monoid




-- a ⍩ _

--  	⍧ 	⍨ 	 	⍪
-- ⋲ 	⋳ 	⋴ 	⋵ 	⋶ 	⋷ 	⋸ 	⋹ 	⋺ 	⋻ 	⋼ 	⋽ 	⋾ 	⋿

-- a ⫙ P
-- ∈down

-- data _∼-⦋⦌_ {U : 𝒰 𝑖} {{_ : isSetoid 𝑗 U}} {P : 𝒫 U} : (a b : ⦋ P ⦌) -> 𝒰 (𝑖 ､ 𝑗) where
--   incl : ∀ {a b x y} -> a ∼ b -> (a ∈ x) ∼-⦋⦌ (b ∈ y)






-- record Arg (A : 𝒰 𝑖) : 𝒰 𝑖 where
--   instance constructor arg
--   field {inside} : A

-- Ideal : ∀ A -> {{R : Arg (Ring 𝑗 on A)}} -> 𝒰 _
-- Ideal A = 𝒫 A :& isSubsetoid :& isSubmonoid :& isSubgroup :& isIdeal



-- Ideal : ∀ (A : 𝒰 𝑖) -> {{R : Ring (𝑖 , 𝑗) on A}} -> 𝒰 _
-- Ideal A {{R}} = Ideal, A {R}



-- record isFinerEquivRel {A : 𝒰 𝑖} (P : A -> A -> 𝒰 𝑗) (Q : A -> A -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
--   field map-∼ : ∀{a b : A} -> P a b -> Q a b



-- cong-[] : {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isSetoid 𝑗 A}} {{_ : isEquivRel R}} -> {{_ : isFinerEquiv R _∼_}} -> ∀{a b : A} -> a ∼ b -> [ a ] ∼ [ b ]
-- cong-[] p = {!!}


-- data _∼-Ideal[_]_ {A} {{R : Arg (Ring 𝑗 on A)}} (a : A) (I : Ideal A) (b : A) : 𝒰 𝑗 where
--   incl : ⟨ I ⟩ (a ⋆ ◡ b) -> a ∼-Ideal[ I ] b

-- data _∼-Ideal[_]_ {A} {{R : Arg (Ring 𝑗 on A)}} (a : A) (I : Ideal A) (b : A) : 𝒰 𝑗 where
--   incl : ⟨ I ⟩ (a ⋆ ◡ b) -> a ∼-Ideal[ I ] b


-- comm-⋆
-- Ideal : Ring 𝑗 -> 𝒰 _
-- Ideal R = {!!}



-- module _ {A} {R : Ring 𝑗 on A} {I : Ideal A {R}} where
--   lem-10 : ∀{a : A} -> a ∼-Ideal[ I ] a
--   lem-10 {a} = incl (transp-Subsetoid (inv-r-⋆ ⁻¹) closed-◌)

--   lem-20 : ∀{a b} -> a ∼-Ideal[ I ] b -> b ∼-Ideal[ I ] a
--   lem-20 {a} {b} (incl x) =
--     let p : ◡ (a ⋆ ◡ b) ∼ b ⋆ (◡ a)
--         p = ◡ (a ⋆ ◡ b) ≣⟨ distr-⋆-◡ ⟩
--             ◡ ◡ b ⋆ ◡ a ≣⟨ double-◡ `cong-⋆` refl ⟩
--             b ⋆ ◡ a     ∎
--     in incl (transp-Subsetoid p (closed-◡ x))

-- module _ {A : 𝒰 𝑖} {R : A -> A -> 𝒰 𝑗} where
--   instance
--     isSetoid:Quot : {{isEquivRel R}} -> isSetoid _ (A /-𝒰 R)
--     isSetoid._∼_ isSetoid:Quot [ a ] [ b ] = R a b
--     isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:Quot) {x = [ x ]} = refl
--     isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:Quot) {x = [ x ]} {y = [ y ]} p = sym p
--     isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:Quot) {x = [ x ]} {y = [ y ]} {z = [ z ]} p q = p ∙ q





-- module _ {R : Ring 𝑗} {I : Ideal R} where
--   instance
--     isEquivRel:∼[] : isEquivRel (RelIdeal I)
--     isEquivRel.refl isEquivRel:∼[] = lem-10
--     isEquivRel.sym isEquivRel:∼[] = lem-20
--     isEquivRel._∙_ isEquivRel:∼[] = lem-30

--     isRing:/-𝒰 : isRing (′ ⟨ R ⟩ /-𝒰 _∼[ ′ ⟨ I ⟩ ′ ]_ ′)
--     isRing:/-𝒰 = ?
