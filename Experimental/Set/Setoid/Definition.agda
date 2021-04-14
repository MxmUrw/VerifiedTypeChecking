
module Verification.Experimental.Set.Setoid.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure


record ∼-Base {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) (a : A) (b : A) : 𝒰 (𝑖 ､ 𝑗) where
  constructor incl
  field ⟨_⟩ : R a b
  -- incl : R a b -> ∼-Base R a b -- a ∼[ R ] b
open ∼-Base public

instance
  isEquivRel:≡∼-Base : ∀{A : 𝒰 𝑖} -> isEquivRel (∼-Base (_≡_ {A = A}))
  isEquivRel.refl isEquivRel:≡∼-Base = incl refl-Path
  isEquivRel.sym isEquivRel:≡∼-Base (incl p) = incl (sym-Path p)
  isEquivRel._∙_ isEquivRel:≡∼-Base (incl p) (incl q) = incl (trans-Path p q)

-- record isSetoid 𝑗 A {{_ : From (𝒰 𝑖) A}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
-- open isTypoid {{...}} public


record isSetoid (𝑗 : 𝔏) (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  -- field _∼_ : A -> A -> 𝒰 𝑗
  --       {{isEquivRel:∼}} : isEquivRel _∼_
  field _∼'_ : A -> A -> 𝒰 𝑗
  _∼_ : A -> A -> 𝒰 (𝑖 ､ 𝑗)
  _∼_ = ∼-Base _∼'_ -- _∼[ _∼'_ ]_

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
  isSetoid:⦋𝒫⦌ : ∀{𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} -> {{_ : isSetoid 𝑗 A}} -> {P : 𝒫 A} -> isSetoid _ ⦋ P ⦌
  isSetoid._∼'_ isSetoid:⦋𝒫⦌ (a ∈ _) (b ∈ _) = a ∼ b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:⦋𝒫⦌) {x = a ∈ x} = incl refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:⦋𝒫⦌) {a ∈ x} {a₁ ∈ x₁} (incl p) = incl (sym p)
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:⦋𝒫⦌) {a ∈ x} {a₁ ∈ x₁} {a₂ ∈ x₂} (incl p) (incl q) = incl (p ∙ q)


--------------------------------------------------------------------------------
-- Subsetoids

record isSubsetoid {𝑗 : 𝔏 ^ 2} {A} {{_ : Setoid 𝑗 on A}} (P : 𝒫 A) : 𝒰 𝑗 where
  field transp-Subsetoid : ∀{a b} -> a ∼ b -> P a -> P b

open isSubsetoid {{...}} public

Subsetoid : {𝑗 : 𝔏 ^ 2} (X : Setoid 𝑗) -> 𝒰 _
Subsetoid X = 𝒫 ⟨ X ⟩ :& isSubsetoid

-- instance
--   isEquivRel:⫗ : ∀{A : 𝒰 𝑖} -> isEquivRel (∼-Base (λ (P Q : A -> 𝒰 𝑗) -> P ⫗ Q))
--   isEquivRel.refl isEquivRel:⫗ = incl ((λ x -> x) , (λ x -> x))
--   isEquivRel.sym isEquivRel:⫗ (incl (P , Q)) = incl (Q , P)
--   isEquivRel._∙_ isEquivRel:⫗ (incl (P₀ , Q₀)) (incl (P₁ , Q₁)) = incl ((λ x -> P₁ (P₀ x)) , (λ x -> Q₀ (Q₁ x)))

instance
  isEquivRel:⫗ : ∀{𝑖 : 𝔏 ^ 2} -> ∀{A : Setoid 𝑖} -> isEquivRel (∼-Base (λ (P Q : Subsetoid A) -> ⟨ P ⟩ ⫗ ⟨ Q ⟩))
  isEquivRel.refl isEquivRel:⫗ = incl ((λ x -> x) , (λ x -> x))
  isEquivRel.sym isEquivRel:⫗ (incl (P , Q)) = incl (Q , P)
  isEquivRel._∙_ isEquivRel:⫗ (incl (P₀ , Q₀)) (incl (P₁ , Q₁)) = incl ((λ x -> P₁ (P₀ x)) , (λ x -> Q₀ (Q₁ x)))

instance
  isSetoid:Subsetoid : ∀{𝑗 : 𝔏 ^ 2} -> {X : Setoid 𝑗} -> isSetoid _ (Subsetoid X)
  isSetoid._∼'_ isSetoid:Subsetoid A B = ⟨ A ⟩ ⫗ ⟨ B ⟩

--------------------------------------------------------------------------------
-- Quotients

data _/-𝒰_ {𝑖 𝑗 : 𝔏} (A : 𝒰 𝑖) (R : A -> A -> 𝒰 𝑗) : 𝒰 (𝑖 ) where
  [_] : A -> A /-𝒰 R


instance
  isSetoid:/-𝒰 : {𝑖 𝑘 : 𝔏} {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> isSetoid _ (A /-𝒰 R)
  isSetoid._∼'_ (isSetoid:/-𝒰 {R = R}) [ a ] [ b ] = R a b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} = incl refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} (incl p) = incl (sym p)
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} {z = [ z ]} (incl p) (incl q) = incl (p ∙ q)

--------------------------------------------------------------------------------
-- Induced setoid


instance
  isSetoid:Family : ∀{A : 𝒰 𝑖} -> {{_ : isSetoid 𝑗 A}} -> ∀{I : 𝒰 𝑘} -> isSetoid _ (I -> A)
  isSetoid._∼'_ isSetoid:Family f g = ∀{a} -> f a ∼ g a
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:Family) = incl (refl)
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:Family) (incl p) = incl (p ⁻¹)
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:Family) (incl p) (incl q) = incl (p ∙ q)


