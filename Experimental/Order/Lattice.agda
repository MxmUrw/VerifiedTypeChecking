
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Order.Lattice where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Meta.Structure


module _ {A : 𝒰 _} {{_ : Preorder 𝑗 on A}} where
  _≚_ : A -> A -> 𝒰 _
  a ≚ b = (a ≤ b) ×-𝒰 (b ≤ a)

module _ {𝑖 : 𝔏 ^ 3} where
  record hasFiniteJoins (A : Preorder 𝑖) : 𝒰 𝑖 where
    field ⊥ : ⟨ A ⟩
          initial-⊥ : ∀{a : ⟨ A ⟩} -> ⊥ ≤ a
    field _∨_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
          ι₀-∨ : {a b : ⟨ A ⟩} -> a ≤ a ∨ b
          ι₁-∨ : {a b : ⟨ A ⟩} -> b ≤ a ∨ b
          [_,_]-∨ : {a b c : ⟨ A ⟩} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c

    infixl 60 _∨_
  open hasFiniteJoins {{...}} public

  record hasFiniteMeets (A : Preorder 𝑖) : 𝒰 𝑖 where
    field ⊤ : ⟨ A ⟩
          initial-⊤ : ∀(a : ⟨ A ⟩) -> a ≤ ⊤
    field _∧_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
          π₀-∧ : {a b : ⟨ A ⟩} -> a ∧ b ≤ a
          π₁-∧ : {a b : ⟨ A ⟩} -> a ∧ b ≤ b
          ⟨_,_⟩-∧ : {a b c : ⟨ A ⟩} -> c ≤ a -> c ≤ b -> c ≤ a ∧ b

    infixl 60 _∧_
  open hasFiniteMeets {{...}} public

  record hasAllJoins (A : Preorder 𝑖) : 𝒰 (𝑖 ⁺) where
    field ⋁ : ∀{X : 𝒰 𝑖} -> (X -> ⟨ A ⟩) -> ⟨ A ⟩
          ι-⋁ : ∀{X F} -> ∀ (x : X) -> F x ≤ ⋁ F
          [_]-⋁ : ∀{X F b} -> (∀(x : X) -> F x ≤ b) -> ⋁ F ≤ b
  open hasAllJoins {{...}} public

CompleteJoinSemilattice : ∀ 𝑖 -> 𝒰 (𝑖 ⁺)
CompleteJoinSemilattice 𝑖 = Preorder 𝑖 :& hasAllJoins

MeetSemilattice : ∀ 𝑖 -> 𝒰 (𝑖 ⁺)
MeetSemilattice 𝑖 = Preorder 𝑖 :& hasFiniteMeets


----------------------------------------------------------
-- Derived instances

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid 𝑗 A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}} where
  instance
    hasFiniteJoins:Family : ∀{I : 𝒰 𝑗} -> hasFiniteJoins (′ (I -> A) ′)
    hasFiniteJoins.⊥         hasFiniteJoins:Family = λ _ -> ⊥
    hasFiniteJoins.initial-⊥ hasFiniteJoins:Family = incl initial-⊥
    hasFiniteJoins._∨_       hasFiniteJoins:Family = λ a b i -> a i ∨ b i
    hasFiniteJoins.ι₀-∨      hasFiniteJoins:Family = incl ι₀-∨
    hasFiniteJoins.ι₁-∨      hasFiniteJoins:Family = incl ι₁-∨
    hasFiniteJoins.[_,_]-∨   hasFiniteJoins:Family = λ f g -> incl [ ⟨ f ⟩ , ⟨ g ⟩ ]-∨



----------------------------------------------------------
-- Categorical Structure


-- unquoteDecl CompleteJoinSemilattice makeCompleteJoinSemilattice = #struct "CompleteJoinSemilattice" (quote hasAllJoins) "A" CompleteJoinSemilattice makeCompleteJoinSemilattice

-- instance
--   POStruc : ∀{a : CompleteJoinSemilattice 𝑖}


-- record isCompleteJoinPreserving {A : CompleteJoinSemilattice 𝑖} {B : CompleteJoinSemilattice 𝑗} (f : (⟨ A ⟩ -> El B) :& isMonotone {A = make& (⟨ A ⟩)}) : 𝒰 (𝑖 ､ 𝑗) where
--   testa : isPreorder (⟨ A ⟩)
--   testa = it


-- testing1 : (A : CompleteJoinSemilattice 𝑖) -> (X : 𝒰 𝑖) -> (F : X -> ⟨ A ⟩) -> 𝒰 𝑖
-- testing1 A X F = ∑ (λ (a : ⟨ A ⟩) -> ∀(x : X) -> a ≤ F x)


{-
record preservesAllJoins {A B} {{_ : CompleteJoinSemilattice 𝑖 on A}} {{_ : CompleteJoinSemilattice 𝑖 on B}} (f : (A -> B) :& isMonotone) : 𝒰 (𝑖 ⁺) where
  field preserves-⋁ : ∀{X} {F : X -> A} -> ⟨ f ⟩ (⋁ F) ≚ ⋁ (λ x -> ⟨ f ⟩ (F x))


record preservesFiniteMeets {A B} {{_ : MeetSemilattice 𝑖 on A}} {{_ : MeetSemilattice 𝑗 on B}} (f : (A -> B) :& isMonotone) : 𝒰 (𝑖 ､ 𝑗) where
  field preserves-∧ : ∀{a b : A} -> ⟨ f ⟩ (a ∧ b) ≚ ⟨ f ⟩ a ∧ ⟨ f ⟩ b
        preserves-⊤ : ⟨ f ⟩ ⊤ ≚ ⊤

-}

