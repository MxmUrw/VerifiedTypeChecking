
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Classes.EquivalenceRelation where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes.Operators.Unary
open import Verification.Conventions.Prelude.Classes.Cast
open import Verification.Conventions.Prelude.Classes.Anything
open import Verification.Conventions.Prelude.Data.StrictId


--------------------------------------------------------------------------------
-- == Equivalence relation
--

-- #Notation/Annotatable# trans
-- #Notation/SemanticCategory# \mathrm{Eqv} = Equiv

-- [Definition]
record IEquiv {X : 𝒰 𝑖} (_≣_ : X -> X -> 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  field refl : ∀{x : X} -> x ≣ x
        sym : ∀{x y : X} -> x ≣ y -> y ≣ x
        _∙_ : ∀{x y z : X} -> x ≣ y -> y ≣ z -> x ≣ z

  infixl 30 _∙_

open IEquiv {{...}} public
-- //

module _ {X : 𝒰 𝑖} {_≣_ : X -> X -> 𝒰 𝑗} {{_ : IEquiv _≣_}} where
  instance
    Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x ≣ y) (y ≣ x)
    Notation-Inverse:Equiv Notation-Inverse.⁻¹ = sym


instance
  IEquiv:Path : {X : 𝒰 𝑖} -> IEquiv (λ (x y : X) -> x ≡ y)
  IEquiv.refl  IEquiv:Path = refl-Path
  IEquiv.sym   IEquiv:Path = sym-Path
  IEquiv._∙_   IEquiv:Path = trans-Path



module _ {X : 𝒰 𝑖} {_∼_ : X -> X -> 𝒰 𝑗} {{_ : IEquiv _∼_}} where
  fromPath : ∀{a b : X} -> a ≡ b -> a ∼ b
  fromPath {a = a} p = transport (λ i -> a ∼ p i) refl

-- sym-Id : ∀{X : 𝒰 𝑖} {x y : X} -> Id x y -> Id y x
-- sym-Id {x = x} {y = y} p = J-Id (λ y _ -> Id y x) refl-Id p

trans-Id : ∀{X : 𝒰 𝑖} {x y z : X} -> Id x y -> Id y z -> Id x z
trans-Id {x = x} {y} {z} p q = J-Id (λ z _ -> Id x z) p q

instance
  IEquiv:Id : {X : 𝒰 𝑖} -> IEquiv (λ (x y : X) -> Id x y)
  IEquiv.refl IEquiv:Id = refl-Id
  IEquiv.sym IEquiv:Id = sym-Id
  IEquiv._∙_ IEquiv:Id = trans-Id

module _ {X : 𝒰 𝑘} {x : X} where
  record ∀Id (P : (y : X) -> Id x y -> 𝒰 𝑙) : 𝒰 (𝑘 ⊔ 𝑙) where
    constructor idproof
    field getProof : ∀{y : X} -> (p : Id x y) -> P y p

  open ∀Id public

  J-∀Id : ∀{P : (y : X) -> Id x y -> 𝒰 𝑙} -> (d : P x refl) -> ∀Id P
  J-∀Id {P = P} d = idproof $ λ p -> (J-Id P d p)

cong₂-Id-helper : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> {a1 : A} {b1 : B} -> (f : A -> B -> C)
                 -> ∀Id (λ a2 (p : Id a1 a2) -> ∀Id (λ b2 (q : Id b1 b2) -> Id (f a1 b1) (f a2 b2)))
cong₂-Id-helper f = J-∀Id (J-∀Id refl)

cong₂-Id : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> {a1 a2 : A} {b1 b2 : B} -> (f : A -> B -> C) -> (Id a1 a2) -> (Id b1 b2) -> Id (f a1 b1) (f a2 b2)
cong₂-Id f p q = cong₂-Id-helper f .getProof p .getProof q

instance
  IEquiv:StrId : {X : 𝒰 𝑖} -> IEquiv (λ (x y : X) -> StrId x y)
  IEquiv.refl IEquiv:StrId = refl-StrId
  IEquiv.sym IEquiv:StrId refl-StrId = refl-StrId
  (IEquiv:StrId IEquiv.∙ refl-StrId) q = q

_≡-Str_ = StrId

instance
  Cast:≡Str : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> Cast (a ≡-Str b) IAnything (a ≡ b)
  Cast.cast Cast:≡Str refl-StrId = refl

≡-Str→≡ : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (a ≡-Str b) -> (a ≡ b)
≡-Str→≡ refl-StrId = refl

≡→≡-Str : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (a ≡ b) -> (a ≡-Str b)
≡→≡-Str {a = a} {b} p = transport (λ i -> a ≡-Str (p i)) refl-StrId

cong-Str : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {a b : A} -> (f : A -> B) -> (a ≡-Str b) -> (f a ≡-Str f b)
cong-Str f refl-StrId = refl-StrId

-- right≢left-Str : ∀{a : A}

≡-change-iso : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (p : a ≡-Str b) -> (≡→≡-Str (≡-Str→≡ p) ≡ p)
≡-change-iso refl-StrId = transportRefl refl-StrId

--------------------------------------------------------------------------------
-- === path syntax

module _ {A : 𝒰 𝑖} {_≣_ : A -> A -> 𝒰 𝑗} {{_ : IEquiv _≣_}} where
  _≣⟨_⟩_ : (x : A) {y : A} {z : A} → x ≣ y → y ≣ z → x ≣ z
  _ ≣⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

  ≣⟨⟩-syntax : (x : A) {y z : A} → x ≣ y → y ≣ z → x ≣ z
  ≣⟨⟩-syntax = _≣⟨_⟩_
  infixr 2 ≣⟨⟩-syntax
  infix  3 _∎
  infixr 2 _≣⟨_⟩_

  _∎ : (x : A) → x ≣ x
  _ ∎ = refl
