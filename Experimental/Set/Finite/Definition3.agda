
module Verification.Experimental.Set.Finite.Definition3 where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice



module _ {A : 𝒰 𝑖} where
  ⦅_⦆ : A -> A -> Prop 𝑖
  ⦅ a ⦆ b = ∣ (a ≡ b) ∣

  data Reachable : {P Q : A -> Prop 𝑖} (_ : P ≤ Q) -> 𝒰 (𝑖 ⁺) where
    refl-Reach : ∀{P : A -> Prop 𝑖} -> Reachable {P} {P} reflexive
    step-Reach : ∀{P Q : A -> Prop 𝑖} -> ∀{a : A}
                 -> (P≤Q : P ≤ Q)
                 -> ⦅ a ⦆ ≰ P -> (Y : ⦅ a ⦆ ≤ Q)
                 -> Reachable {P ∨ ⦅ a ⦆} {Q} [ P≤Q , Y ]-∨
                 -> Reachable {P} {Q} P≤Q

  comp-Reach : ∀{P Q R : A -> Prop 𝑖} {X : P ≤ Q} {Y : Q ≤ R} -> Reachable X -> Reachable Y -> Reachable (X ⟡ Y)
  comp-Reach refl-Reach q = q
  comp-Reach (step-Reach _ x Y p) q = {!!} -- step-Reach ? x ? (comp-Reach p q)

record 𝒫-Dec (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  constructor _,_
  field ⟨_⟩ : A -> Prop 𝑖
  field Proof : ∀ a -> Decision (Prop.⟨_⟩ (⟨_⟩ a))
open 𝒫-Dec public


-- 𝒫-Dec : (A : 𝒰 𝑖) -> 𝒰 (𝑖 ⁺)
-- 𝒫-Dec {𝑖} A = (A -> Prop 𝑖) :& (λ P -> ∀ a -> Decision ⟨ P a ⟩)

record isFinite (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field reach : ∀ (P Q : 𝒫-Dec A) -> (R : ⟨ P ⟩ ≤ ⟨ Q ⟩) -> Reachable R
open isFinite {{...}} public

Finite : (𝑖 : 𝔏) -> 𝒰 _
Finite 𝑖 = 𝒰 𝑖 :& isFinite

-- size : Finite 𝑖 -> ℕ
-- size A = f ⟨ A ⟩ (⊥ , {!!}) {!!} {!!} (reach _ _ _)
--   where f : ∀(A : 𝒰 𝑖) (P Q : 𝒫-Dec A) -> (R : ⟨ P ⟩ ≤ ⟨ Q ⟩) -> Reachable R -> ℕ
--         f A P (.(⟨ P ⟩) , Proof₁) (incl .(isPreorder.reflexive isPreorder:Prop)) refl-Reach = 0
--         f A P Q R (step-Reach .R x Y r) = suc (f _ _ _ _ r)


