
{-# OPTIONS --cubical --no-import-sorts #-}

module Verification.Conventions.Proprelude.Init where

open import Verification.Conventions.Proprelude.Imports

--------------------------------------------------------------------------------
-- Universe levels
ℓ₀ = lzero
ℓ₁ = ℓ₀ ⁺
ℓ₂ = ℓ₁ ⁺

module PrimitiveUniverseNotation where
  -- variables for multilevels
  variable
    ℓ ℓ' 𝑖 𝑗 𝑘 𝑙 𝑚 : 𝔏

  open import Agda.Primitive public using () renaming (Set to 𝒰)
  -- renaming
  -- (Level to 𝔏; lsuc to _⁺ ; Setω to 𝒰ω ; Set to 𝒰' ; Prop to CompProp ; _⊔_ to join-𝔏
  -- )

  -- 𝒰 : (l : 𝔏) -> 𝒰' (l ⁺)
  -- 𝒰 l = 𝒰' l

open PrimitiveUniverseNotation

-- introducing the syntax
record IJoinable (X : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field _⊔_ : X -> X -> X
  infixl 6 _⊔_
open IJoinable {{...}} public

-- instance for universe levels
instance
  IJoinable:𝔏 : IJoinable 𝔏
  IJoinable._⊔_ IJoinable:𝔏 = join-𝔏

--------------------------------------------------------------------------------
-- Preparing extended syntax

∆ : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (b : B) -> A -> B
∆ b _ = b

∏_ : ∀{A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> 𝒰 (ℓ ⊔ ℓ')
∏_ {A = A} B = (∀ (a : A) -> B a)

∑_ : ∀{A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> 𝒰 (ℓ ⊔ ℓ')
∑_ {A = A} B = Σ A B

infixr 30 _×-𝒰_
_×-𝒰_ : 𝒰 ℓ -> 𝒰 ℓ' -> 𝒰 (ℓ ⊔ ℓ')
A ×-𝒰 B = ∑ λ (a : A) -> B



-- instance
--   IIndexable:^2 : ∀{X : 𝒰 𝑖} -> IIndexable (X ^ 2) 𝟚 (∆ X)
--   (IIndexable:^2 IIndexable.⌄ x) ₀ = x .fst
--   (IIndexable:^2 IIndexable.⌄ x) ₁ = x .snd

--   IIndexable:^3 : ∀{X : 𝒰 𝑖} -> IIndexable (X ^ 3) 𝟛 (∆ X)
--   (IIndexable:^3 IIndexable.⌄ x) ₀ = x .fst
--   (IIndexable:^3 IIndexable.⌄ x) ₁ = x .snd .fst
--   (IIndexable:^3 IIndexable.⌄ x) ₂ = x .snd .snd

-- variable
--   𝑖𝑖 𝑗𝑗 𝑘𝑘 : 𝔏 ^ (suc (suc zero))
--   𝑖𝑖𝑖 𝑗𝑗𝑗 𝑘𝑘𝑘 : 𝔏 ^ (suc (suc (suc zero)))


--------------------------------------------------------------------------------
-- Extended syntax



-- instance
--   IMultiJoinable:𝟚-Family : ∀{X : 𝒰 𝑖} {{_ : IJoinable X}} -> IMultiJoinable (X ^ 2) X
--   IMultiJoinable.⨆ IMultiJoinable:𝟚-Family x = x ⌄ ₀ ⊔ x ⌄ ₁

--   IMultiJoinable:𝟛-Family : ∀{X : 𝒰 𝑖} {{_ : IJoinable X}} -> IMultiJoinable (X ^ 3) X
--   IMultiJoinable.⨆ IMultiJoinable:𝟛-Family x = x ⌄ ₀ ⊔ x ⌄ ₁ ⊔ x ⌄ ₂


-- joinL : 𝔏 ^ 3 -> 𝔏 ^ 3 -> 𝔏 ^ 3
-- joinL I J = let x = ⨆ I ⊔ ⨆ J
--             in x , x , x

-- zipL : 𝔏 ^ 3 -> 𝔏 ^ 3 -> 𝔏 ^ 3
-- zipL 𝑖𝑖𝑖 𝑗𝑗𝑗 = 𝑖𝑖𝑖 ⌄ ₀ ⊔ 𝑗𝑗𝑗 ⌄ ₀ , 𝑖𝑖𝑖 ⌄ ₁ ⊔ 𝑗𝑗𝑗 ⌄ ₁ , 𝑖𝑖𝑖 ⌄ ₂ ⊔ 𝑗𝑗𝑗 ⌄ ₂



--------------------------------------------------------------------------------
-- alternative set syntax





id-Path : ∀{A : 𝒰 𝑖} -> {a : A} -> a ≡ a
id-Path {a = a} = λ _ -> a

Image : ∀{A : 𝒰 𝑖} {B : 𝒰 (𝑗)} -> (A -> B) -> 𝒰 (𝑖 ⊔ 𝑗)
Image f = ∑ λ b -> ∑ λ a -> f a ≡ b

module _ {A : 𝒰 𝑖} where
  funExt⁻¹ : {B : A → I → 𝒰 ℓ'}
    {f : (x : A) → B x i0} {g : (x : A) → B x i1}
    → PathP (λ i → (x : A) → B x i) f g
    → ((x : A) → PathP (B x) (f x) (g x))
  funExt⁻¹ p x i = p i x


cong₂ : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> (f : A -> B -> C) -> {a1 a2 : A} -> {b1 b2 : B} -> (p : a1 ≡ a2) -> (q : b1 ≡ b2) -> f a1 b1 ≡ f a2 b2
cong₂ f p q i = f (p i) (q i)
-- infixr 30 _×-𝒰_
-- _×-𝒰_ : 𝒰 ℓ -> 𝒰 ℓ' -> 𝒰 (ℓ ⊔ ℓ')
-- A ×-𝒰 B = ∑ λ (a : A) -> B

-------------------------
-- special functions

pattern ↥ x = lift x
↧ = lower

it : ∀{A : 𝒰 𝑖} -> {{a : A}} -> A
it {{a}} = a

-- const : ∀{A : 𝒰 ℓ} {B : 𝒰 ℓ'} -> B -> A -> B
-- const b _ = b

-- _∘_ : {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘}
--       -> (B -> C) -> (A -> B)
--       -> A -> C
-- f ∘ g = λ a -> f (g a)

infixr -20 _$_
_$_ : ∀{A : 𝒰 ℓ} {B : 𝒰 ℓ'} -> (A -> B) -> A -> B
f $ a = f a

module TypeNotation where
  infixr 30 _×_
  _×_ = _×-𝒰_


