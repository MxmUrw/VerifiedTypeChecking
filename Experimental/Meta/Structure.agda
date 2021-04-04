
module Verification.Experimental.Meta.Structure where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)

record ∑i_ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  instance constructor make∑i
  -- field overlap {{ifst}} : A
  field {ifst} : A
  field overlap {{isnd}} : B (ifst)
open ∑i_ {{...}} public


record hasU (A : 𝒰 𝑖) 𝑗 𝑘 : 𝒰 (𝑖 ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
  field getU : 𝒰 𝑗
  field getP : getU -> 𝒰 𝑘
  field reconstruct : ∑ getP -> A
  field destructEl : A -> getU
  field destructP : (a : A) -> getP (destructEl a)
open hasU public


record _:&_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) : 𝒰 (𝑗 ､ 𝑘 ､ 𝑙) where
  constructor ′_′
  field ⟨_⟩ : getU U
  -- field overlap {{oldProof}} : getP U ⟨_⟩
  field {oldProof} : getP U ⟨_⟩
  field overlap {{Proof}} : P (reconstruct U (⟨_⟩ , oldProof))
open _:&_ {{...}} public hiding (⟨_⟩)
open _:&_ public using (⟨_⟩)

-- pattern ′_′ = ′_′
infixl 30 _:&_


{-
-- A test for getting a better syntax for casting, i.e., what we currently do with ′ ⟨ A ⟩ ′.
-- But it doesn't work because we have to use an intermediary type result `resType`
-- since we need to pattern-match on refl to get the proof that the two universes
-- of U and of U2 are the same.
-- But then at the call site the type `resType` does not match with the wanted
-- actual type `... :& ...`
resType : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} (a : UU)
        -> (UU2 : 𝒰 𝑖₂) {{U2 : hasU UU2 𝑘 𝑙₂}} -> (P2 : UU2 -> 𝒰 𝑗₂) -> (getU U ≡-Str getU U2) -> 𝒰 _
resType {UU = UU} {{U}} a UU2 {{U2}} P2 refl-StrId =
        {{oldProof : getP U2 (destructEl U a)}}
        -> {{_ : P2 (reconstruct U2 (destructEl U a , oldProof))}}
        -> UU2 :& P2

% : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} (a : UU)
  -> {UU2 : 𝒰 𝑖₂} {{U2 : hasU UU2 𝑘 𝑙₂}} {P2 : UU2 -> 𝒰 𝑗₂}
     -> {{pp : (getU U ≡-Str getU U2)}}
     -> resType a UU2 P2 pp
% {UU = UU} {{U}} a {UU2} {{U2}} {P2} {{refl-StrId}} {{oldProof}} {{newProof}} = ′ destructEl U a ′
-}

record _:>_ {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) (Q : UU :& P -> 𝒰 𝑗₂) (a : UU) : 𝒰 (𝑗 ､ 𝑗₂ ､ 𝑘 ､ 𝑙) where
  instance constructor make:>
  field overlap {{Proof1}} : P (reconstruct U (destructEl U a , destructP U a))
  field overlap {{Proof2}} : Q (′_′ (destructEl U a) {destructP U a} {{Proof1}})

-- record _:&2_:∣_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) (Q : UU -> 𝒰 𝑗₂) : 𝒰 (𝑗 ､ 𝑗₂ ､ 𝑘 ､ 𝑙) where
--   constructor ′_′2
--   field El : getU U
--   field overlap {{oldProof2}} : getP U El
--   field overlap {{Proof2-P}} : P (reconstruct U (El , oldProof2))
--   field overlap {{Proof2-Q}} : Q (reconstruct U (El , oldProof2))
-- open _:&2_:∣_ {{...}} public hiding (El)
-- open _:&2_:∣_ public using (El)

-- infixl 30 _:&2_:∣_

-- instance
--   ElPrev : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) -> 

record _:,_ {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) (Q : UU -> 𝒰 𝑗₂) (a : UU) : 𝒰 (𝑗 ､ 𝑗₂) where
  instance constructor make,
  field overlap {{Proof1}} : P a
  field overlap {{Proof2}} : Q a
open _:,_ {{...}} public

infixr 80 _:,_

record isAnything {A : 𝒰 𝑖} (a : A) (𝑗 : 𝔏) : 𝒰 (𝑗) where

instance
  isAnything:anything : {A : 𝒰 𝑖} {a : A} {𝑗 : 𝔏} -> isAnything a 𝑗
  isAnything:anything = record {}

-- instance
--   hasU:𝒰 : ∀{𝑖 𝑗 : 𝔏} -> hasU (𝒰 𝑖) (𝑖 ⁺) (𝑖 ⁺ ⊔ 𝑗)
--   getU (hasU:𝒰 {𝑖}) = 𝒰 𝑖
--   getP (hasU:𝒰 {𝑖} {𝑗 = 𝑗}) u = isAnything u 𝑗

instance
  hasU:𝒰 : ∀{𝑖 : 𝔏} -> hasU (𝒰 𝑖) (𝑖 ⁺) (ℓ₀)
  getU (hasU:𝒰 {𝑖}) = 𝒰 𝑖
  getP (hasU:𝒰 {𝑖}) u = isAnything u ℓ₀
  reconstruct (hasU:𝒰 {𝑖}) (x , _) = x
  destructEl (hasU:𝒰 {𝑖}) a = a
  destructP (hasU:𝒰 {𝑖}) a = record {}

instance
  hasU:Exp : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> hasU (A -> B) _ _
  getU (hasU:Exp {A = A} {B}) = A -> B
  getP (hasU:Exp {𝑖} {𝑗} {A = A} {B}) u = isAnything u (ℓ₀)
  reconstruct (hasU:Exp {A = A} {B}) (x , _) = x
  destructEl (hasU:Exp {A = A} {B}) f = f
  destructP (hasU:Exp {A = A} {B}) _ = record {}

instance
  hasU:& : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} {P : UU -> 𝒰 𝑗} -> hasU (UU :& P) _ _
  getU (hasU:& {UU = A} {{U}}) = getU U
  getP (hasU:& {UU = A} {{U}} {P = P}) a = ∑i λ (p1 : getP U a) -> P (reconstruct U (a , p1))
  reconstruct (hasU:& {UU = A} {{U}} {P = P}) (a , pa) = ′_′ a {pa .ifst} {{pa .isnd}}
  destructEl (hasU:& {UU = A} ⦃ U ⦄ {P = P}) (′_′ a) = a
  destructP (hasU:& {UU = A} {{U}} {P = P}) (′_′ a ) = make∑i -- {ifst = pold}

_on_ : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} -> (a : getU U) -> 𝒰 _
_on_ UU {{U}} a = getP U a


