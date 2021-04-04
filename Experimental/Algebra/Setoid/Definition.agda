
module Verification.Experimental.Algebra.Setoid.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure


record RR {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) (a : A) (b : A) : 𝒰 (𝑖 ､ 𝑗) where
  constructor incl
  field ⟨_⟩ : R a b
  -- incl : R a b -> RR R a b -- a ∼[ R ] b
open RR public

instance
  isEquivRel:≡RR : ∀{A : 𝒰 𝑖} -> isEquivRel (RR (_≡_ {A = A}))
  isEquivRel.refl isEquivRel:≡RR = incl refl-Path
  isEquivRel.sym isEquivRel:≡RR (incl p) = incl (sym-Path p)
  isEquivRel._∙_ isEquivRel:≡RR (incl p) (incl q) = incl (trans-Path p q)

-- record isSetoid 𝑗 A {{_ : From (𝒰 𝑖) A}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
-- open isTypoid {{...}} public


record isSetoid (𝑗 : 𝔏) (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  -- field _∼_ : A -> A -> 𝒰 𝑗
  --       {{isEquivRel:∼}} : isEquivRel _∼_
  field myRel : A -> A -> 𝒰 𝑗
  _∼_ : A -> A -> 𝒰 (𝑖 ､ 𝑗)
  _∼_ = RR myRel -- _∼[ myRel ]_

  field {{isEquivRel:∼}} : isEquivRel _∼_

  _≁_ : A -> A -> 𝒰 (𝑖 ､ 𝑗)
  _≁_ a b = ¬ a ∼ b
open isSetoid {{...}} public

Setoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Setoid 𝑗 = 𝒰 (𝑗 ⌄ 0) :& isSetoid (𝑗 ⌄ 1)

record isSetoidHom {𝑖 𝑗 : 𝔏 ^ 2} (A : Setoid 𝑖) (B : Setoid 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  field preserves-∼ : ∀{a b} -> a ∼ b -> f a ∼ f b
open isSetoidHom {{...}} public


instance
  isSetoid:𝒫 : ∀{𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} -> {{_ : isSetoid 𝑗 A}} -> {P : 𝒫 A} -> isSetoid _ ⦋ P ⦌
  isSetoid.myRel isSetoid:𝒫 (a ∈ _) (b ∈ _) = a ∼ b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:𝒫) {x = a ∈ x} = incl refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:𝒫) {a ∈ x} {a₁ ∈ x₁} (incl p) = incl (sym p)
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:𝒫) {a ∈ x} {a₁ ∈ x₁} {a₂ ∈ x₂} (incl p) (incl q) = incl (p ∙ q)

record isSubsetoid {𝑗 : 𝔏 ^ 2} {A} {{_ : Setoid 𝑗 on A}} (P : 𝒫 A) : 𝒰 𝑗 where
  field transp-Subsetoid : ∀{a b} -> a ∼ b -> P a -> P b

open isSubsetoid {{...}} public


data _/-𝒰_ {𝑖 𝑗 : 𝔏} (A : 𝒰 𝑖) (R : A -> A -> 𝒰 𝑗) : 𝒰 (𝑖 ) where
  [_] : A -> A /-𝒰 R


instance
  isSetoid:/-𝒰 : {𝑖 𝑘 : 𝔏} {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> isSetoid _ (A /-𝒰 R)
  isSetoid.myRel (isSetoid:/-𝒰 {R = R}) [ a ] [ b ] = R a b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} = incl refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} (incl p) = incl (sym p)
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} {z = [ z ]} (incl p) (incl q) = incl (p ∙ q)




