
module Verification.Experimental.Algebra3.Typoid.Definition where

open import Verification.Conventions hiding (⟪_⟫ ; Structure ; ′_′ ; ⟨_⟩)
open import Verification.Experimental.Meta.Structure5


record isLogic (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field isTrue : A -> 𝒰 𝑖
  field _⇒_ : A -> A -> A
  field _∧_ : A -> A -> A
  field isTrue-And : ∀(a b : A) -> isTrue a -> isTrue b -> isTrue (a ∧ b)
open isLogic {{...}} public

Logic : (𝑖 : 𝔏) -> 𝒰 (𝑖 ⁺)
Logic 𝑖 = Structure (isLogic {𝑖 = 𝑖})

record isEquivRel2 {A : 𝒰 𝑖} (L : 𝒰 𝑖) {{_ : isLogic L}} (R : A -> A -> L) : 𝒰 𝑖 where
  field refl2 : ∀{a : A} -> isTrue (R a a)
  field sym2 : ∀{a b : A} -> isTrue (R a b ⇒ R b a)
  -- field trans2 : ∀{a b c : A} -> isTrue (R a b ∧ R b c ⇒ )

{-


record isTypoid 𝑗 A {{_ : From (𝒰 𝑖) A}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field _∼_ : A -> A -> 𝒰 𝑗
        {{isEquivRel:∼}} : isEquivRel _∼_
open isTypoid {{...}} public

Typoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Typoid 𝑗 = Structure (From (𝒰 (𝑗 ⌄ 0)) :> isTypoid (𝑗 ⌄ 1))
-- 𝒰 (𝑗 ⌄ 0) :& isTypoid (𝑗 ⌄ 1)

-- record isTypoidHom A B {{_ : Typoid 𝑖 on A}} {{_ : Typoid 𝑗 on B}} (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
--   field preserves-∼ : ∀{a b} -> a ∼ b -> f a ∼ f b
-- open isTypoidHom {{...}} public

record isTypoidHom (A : Typoid 𝑖) (B : Typoid 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  field preserves-∼ : ∀{a b} -> a ∼ b -> f a ∼ f b
open isTypoidHom {{...}} public


{-
instance
  -- isTypoid:𝒫 : ∀{A : 𝒰 𝑖} -> {{_ : _on_ (Typoid 𝑗) {{{!!}}} A}} -> {P : 𝒫 A} -> isTypoid _ ⦋ P ⦌
  isTypoid:𝒫 : ∀{A : 𝒰 𝑖} -> {{_ : (From _ :> isTypoid 𝑗) A}} -> {P : 𝒫 A} -> isTypoid _ ⦋ P ⦌
  isTypoid._∼_ isTypoid:𝒫 (a ∈ _) (b ∈ _) = a ∼ b
  isEquivRel.refl (isTypoid.isEquivRel:∼ isTypoid:𝒫) {x = a ∈ x} = refl
  isEquivRel.sym (isTypoid.isEquivRel:∼ isTypoid:𝒫) {a ∈ x} {a₁ ∈ x₁} p = sym p
  isEquivRel._∙_ (isTypoid.isEquivRel:∼ isTypoid:𝒫) {a ∈ x} {a₁ ∈ x₁} {a₂ ∈ x₂} p q = p ∙ q
  -}

record isSubtypoid {A} {{_ : Typoid 𝑗 on A}} P {{_ : From (𝒫 A) P}} : 𝒰 𝑗 where
  field transp-Subtypoid : ∀{a b} -> a ∼ b -> P a -> P b

open isSubtypoid {{...}} public


data _/-𝒰_ (A : 𝒰 𝑖) (R : A -> A -> 𝒰 𝑗) : 𝒰 (𝑖 ) where
  [_] : A -> A /-𝒰 R


instance
  isFrom:/-𝒰 : {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> From _ (A /-𝒰 R)
  isFrom:/-𝒰 = record {}

  isTypoid:/-𝒰 : {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> isTypoid _ (A /-𝒰 R)
  isTypoid._∼_ (isTypoid:/-𝒰 {R = R}) [ a ] [ b ] = R a b
  isEquivRel.refl (isTypoid.isEquivRel:∼ isTypoid:/-𝒰) {x = [ x ]} = refl
  isEquivRel.sym (isTypoid.isEquivRel:∼ isTypoid:/-𝒰) {x = [ x ]} {y = [ y ]} p = sym p
  isEquivRel._∙_ (isTypoid.isEquivRel:∼ isTypoid:/-𝒰) {x = [ x ]} {y = [ y ]} {z = [ z ]} p q = p ∙ q

  isTypoidOn:/-𝒰 : {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> (_ :> isTypoid _) (A /-𝒰 R)
  _:>_.Proof1 isTypoidOn:/-𝒰 = record {}
  _:>_.Proof2 isTypoidOn:/-𝒰 = it

{-
-}
-}


