
module Verification.Experimental.Meta.Structure where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)

record ∑i_ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  instance constructor make∑i
  field overlap {{ifst}} : A
  field overlap {{isnd}} : B (ifst)
open ∑i_ {{...}} public

record hasU (A : 𝒰 𝑖) 𝑗 𝑘 : 𝒰 (𝑖 ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
  field getU : 𝒰 𝑗
  field getP : getU -> 𝒰 𝑘
  field reconstruct : ∑ getP -> A
open hasU public

record _:&_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) : 𝒰 (𝑗 ､ 𝑘 ､ 𝑙) where
  constructor make&
  field El : getU U
  field overlap {{oldProof}} : getP U El
  field overlap {{Proof}} : P (reconstruct U (El , oldProof))
open _:&_ {{...}} public hiding (El)
open _:&_ public using (El)

infixl 30 _:&_

-- instance
--   ElPrev : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) -> 

record _:,_ {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) (Q : UU -> 𝒰 𝑗₂) (a : UU) : 𝒰 (𝑗 ､ 𝑗₂) where
  constructor make,
  field overlap {{Proof1}} : P a
  field overlap {{Proof2}} : Q a

infixr 80 _:,_

record isAnything {A : 𝒰 𝑖} (a : A) (𝑗 : 𝔏) : 𝒰 (𝑖 ⊔ 𝑗) where

instance
  isAnything:anything : {A : 𝒰 𝑖} {a : A} {𝑗 : 𝔏} -> isAnything a 𝑗
  isAnything:anything = record {}

-- instance
--   hasU:𝒰 : ∀{𝑖 𝑗 : 𝔏} -> hasU (𝒰 𝑖) (𝑖 ⁺) (𝑖 ⁺ ⊔ 𝑗)
--   getU (hasU:𝒰 {𝑖}) = 𝒰 𝑖
--   getP (hasU:𝒰 {𝑖} {𝑗 = 𝑗}) u = isAnything u 𝑗

instance
  hasU:𝒰 : ∀{𝑖 : 𝔏} -> hasU (𝒰 𝑖) (𝑖 ⁺) (𝑖 ⁺)
  getU (hasU:𝒰 {𝑖}) = 𝒰 𝑖
  getP (hasU:𝒰 {𝑖}) u = isAnything u 𝑖
  reconstruct (hasU:𝒰 {𝑖}) (x , _) = x

instance
  hasU:Exp : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> hasU (A -> B) _ _
  getU (hasU:Exp {A = A} {B}) = A -> B
  getP (hasU:Exp {𝑖} {𝑗} {A = A} {B}) u = isAnything u (ℓ₀)
  reconstruct (hasU:Exp {A = A} {B}) (x , _) = x

instance
  hasU:& : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} {P : UU -> 𝒰 𝑗} -> hasU (UU :& P) _ _
  getU (hasU:& {UU = A} {{U}}) = getU U
  getP (hasU:& {UU = A} {{U}} {P = P}) a = ∑i λ (p1 : getP U a) -> P (reconstruct U (a , p1))
  reconstruct (hasU:& {UU = A} {{U}} {P = P}) (a , pa) = make& a -- {{pa .ifst}} {{pa .isnd}}

_on_ : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} -> (a : getU U) -> 𝒰 _
_on_ UU {{U}} a = getP U a


