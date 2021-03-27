
module Verification.Experimental.Algebra.Setoid.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure


record isSetoid (𝑗 : 𝔏) (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field _∼_ : A -> A -> 𝒰 𝑗
        {{isEquivRel:∼}} : isEquivRel _∼_
open isSetoid {{...}} public

Setoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Setoid 𝑗 = 𝒰 (𝑗 ⌄ 0) :& isSetoid (𝑗 ⌄ 1)

record isSetoidHom (A : Setoid 𝑖) (B : Setoid 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  field preserves-∼ : ∀{a b} -> a ∼ b -> f a ∼ f b
open isSetoidHom {{...}} public


instance
  isSetoid:𝒫 : ∀{A : 𝒰 𝑖} -> {{_ : isSetoid 𝑗 A}} -> {P : 𝒫 A} -> isSetoid _ ⦋ P ⦌
  isSetoid._∼_ isSetoid:𝒫 (a ∈ _) (b ∈ _) = a ∼ b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:𝒫) {x = a ∈ x} = refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:𝒫) {a ∈ x} {a₁ ∈ x₁} p = sym p
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:𝒫) {a ∈ x} {a₁ ∈ x₁} {a₂ ∈ x₂} p q = p ∙ q

record isSubsetoid {A} {{_ : Setoid 𝑗 on A}} (P : 𝒫 A) : 𝒰 𝑗 where
  field transp-Subsetoid : ∀{a b} -> a ∼ b -> P a -> P b

open isSubsetoid {{...}} public


data _/-𝒰_ (A : 𝒰 𝑖) (R : A -> A -> 𝒰 𝑗) : 𝒰 (𝑖 ) where
  [_] : A -> A /-𝒰 R


instance
  isSetoid:/-𝒰 : {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> isSetoid _ (A /-𝒰 R)
  isSetoid._∼_ (isSetoid:/-𝒰 {R = R}) [ a ] [ b ] = R a b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} = refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} p = sym p
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} {z = [ z ]} p q = p ∙ q




