
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra.Ring where


open import Verification.Conventions
-- open import Verification.Core.Category.Definition

open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Monoid

record isSemiring (A : Monoid 𝑗 :& isCommutative) : 𝒰 𝑗 where
  field _⋅_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        ⨡ : ⟨ A ⟩
        unit-l-⋅ : ∀{a} -> ⨡ ⋅ a ∼ a
        unit-r-⋅ : ∀{a} -> a ⋅ ⨡ ∼ a
        assoc-l-⋅ : ∀{a b c} -> (a ⋅ b) ⋅ c ∼ a ⋅ (b ⋅ c)
        distr-l-⋅ : ∀{a b c : ⟨ A ⟩} -> a ⋅ (b ⋆ c) ∼ a ⋅ b ⋆ a ⋅ c
        distr-r-⋅ : ∀{a b c : ⟨ A ⟩} -> (b ⋆ c) ⋅ a ∼ b ⋅ a ⋆ c ⋅ a
  infixl 80 _⋅_
open isSemiring {{...}} public

Semiring : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Semiring 𝑗 = (Monoid 𝑗 :& isCommutative) :& isSemiring


record isRing (A : Monoid 𝑗 :& (isCommutative :> isSemiring) :, isGroup) : 𝒰 𝑗 where

Ring : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Ring 𝑗 = (Monoid 𝑗 :& (isCommutative :> isSemiring) :, isGroup) :& isRing

𝒫 : (A : 𝒰 𝑖) -> 𝒰 (𝑖 ⁺)
𝒫 {𝑖} A = A -> 𝒰 𝑖

data ⦋_⦌ {U : 𝒰 𝑖} (P : 𝒫 U) : 𝒰 𝑖 where
  _∈_ : (a : U) -> P a -> ⦋ P ⦌

-- data _∼-⦋⦌_ {U : 𝒰 𝑖} {{_ : isSetoid 𝑗 U}} {P : 𝒫 U} : (a b : ⦋ P ⦌) -> 𝒰 (𝑖 ､ 𝑗) where
--   incl : ∀ {a b x y} -> a ∼ b -> (a ∈ x) ∼-⦋⦌ (b ∈ y)



instance
  isSetoid:𝒫 : ∀{A : 𝒰 𝑖} -> {{_ : isSetoid 𝑗 A}} -> {P : 𝒫 A} -> isSetoid _ ⦋ P ⦌
  isSetoid._∼_ isSetoid:𝒫 (a ∈ _) (b ∈ _) = a ∼ b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:𝒫) {x = a ∈ x} = refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:𝒫) {a ∈ x} {a₁ ∈ x₁} p = sym p
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:𝒫) {a ∈ x} {a₁ ∈ x₁} {a₂ ∈ x₂} p q = p ∙ q

record isSubsetoid {A} {{_ : Setoid 𝑗 on A}} (P : 𝒫 A) : 𝒰 𝑗 where
  field transp-Subsetoid : ∀{a b} -> a ∼ b -> P a -> P b
open isSubsetoid {{...}} public
record isSubmonoid {A} {{_ : Monoid 𝑗 on A}} (P : 𝒫 A :& isSubsetoid) : 𝒰 𝑗 where
  field closed-◌ : ⟨ P ⟩ ◌
        closed-⋆ : ∀{a b} -> ⟨ P ⟩ a -> ⟨ P ⟩ b -> ⟨ P ⟩ (a ⋆ b)
open isSubmonoid {{...}} public

record isSubgroup {A} {{_ : Group 𝑗 on A}} (P : 𝒫 A :& isSubsetoid :& isSubmonoid) : 𝒰 𝑗 where
  field closed-◡ : ∀{a} -> ⟨ P ⟩ a -> ⟨ P ⟩ (◡ a)
open isSubgroup {{...}} public

record isIdeal {A} {{_ : Ring 𝑗 on A}} (P : 𝒫 A :& isSubsetoid :& isSubmonoid :& isSubgroup) : 𝒰 𝑗 where
  field ideal-l-⋅ : ∀{a b} -> ⟨ P ⟩ b -> ⟨ P ⟩ (a ⋅ b)
        ideal-r-⋅ : ∀{a b} -> ⟨ P ⟩ a -> ⟨ P ⟩ (a ⋅ b)
open isIdeal {{...}} public

record Arg (A : 𝒰 𝑖) : 𝒰 𝑖 where
  instance constructor arg
  field {inside} : A

-- Ideal : ∀ A -> {{R : Arg (Ring 𝑗 on A)}} -> 𝒰 _
-- Ideal A = 𝒫 A :& isSubsetoid :& isSubmonoid :& isSubgroup :& isIdeal

Subgroup : (G : Group 𝑗) -> 𝒰 _
Subgroup G = 𝒫 ⟨ G ⟩ :& isSubsetoid :& isSubmonoid :& isSubgroup

Ideal : (R : Ring 𝑗) -> 𝒰 _
Ideal R = 𝒫 ⟨ R ⟩ :& isSubsetoid :& isSubmonoid :& isSubgroup :& isIdeal

-- Ideal : ∀ (A : 𝒰 𝑖) -> {{R : Ring (𝑖 , 𝑗) on A}} -> 𝒰 _
-- Ideal A {{R}} = Ideal, A {R}
record isPrime {R : Ring 𝑗} (I : Ideal R) : 𝒰 𝑗 where
  field prime : ∀{a b} -> ⟨ I ⟩ (a ⋅ b) -> ⟨ I ⟩ a +-𝒰 ⟨ I ⟩ b


data _/-𝒰_ (A : 𝒰 𝑖) (R : A -> A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  [_] : A -> A /-𝒰 R

-- record isFinerEquivRel {A : 𝒰 𝑖} (P : A -> A -> 𝒰 𝑗) (Q : A -> A -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
--   field map-∼ : ∀{a b : A} -> P a b -> Q a b


instance
-- -> {{_ : isFinerEquiv R _∼_}} 
-- {{_ : isSetoid 𝑗 A}} -> 
  isSetoid:/-𝒰 : {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> isSetoid _ (A /-𝒰 R)
  isSetoid._∼_ (isSetoid:/-𝒰 {R = R}) [ a ] [ b ] = R a b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} = refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} p = sym p
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} {z = [ z ]} p q = p ∙ q

-- cong-[] : {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isSetoid 𝑗 A}} {{_ : isEquivRel R}} -> {{_ : isFinerEquiv R _∼_}} -> ∀{a b : A} -> a ∼ b -> [ a ] ∼ [ b ]
-- cong-[] p = {!!}

data RelSubgroup {G : Group 𝑗} (H : Subgroup G) (a : ⟨ G ⟩) (b : ⟨ G ⟩) : 𝒰 𝑗 where
  incl : ⟨ H ⟩ (a ⋆ ◡ b) -> RelSubgroup H a b

-- data _∼-Ideal[_]_ {A} {{R : Arg (Ring 𝑗 on A)}} (a : A) (I : Ideal A) (b : A) : 𝒰 𝑗 where
--   incl : ⟨ I ⟩ (a ⋆ ◡ b) -> a ∼-Ideal[ I ] b

-- data _∼-Ideal[_]_ {A} {{R : Arg (Ring 𝑗 on A)}} (a : A) (I : Ideal A) (b : A) : 𝒰 𝑗 where
--   incl : ⟨ I ⟩ (a ⋆ ◡ b) -> a ∼-Ideal[ I ] b


-- comm-⋆
-- Ideal : Ring 𝑗 -> 𝒰 _
-- Ideal R = {!!}

{-
-}

