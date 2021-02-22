
module Verification.Unification.Instance.Signature where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Type
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Unification.RecAccessible

open import Verification.Core.Syntax.SignatureZ

instance
  IDiscreteStr:Vec : ∀{A : 𝒰 𝑖} {{_ : IDiscreteStr A}} -> IDiscreteStr (Vec A n)
  (IDiscreteStr:Vec IDiscreteStr.≟-Str a) b = {!!}

  IDiscreteStr:ℕ : IDiscreteStr ℕ
  IDiscreteStr:ℕ = {!!}


module _ {K : 𝒰₀} {{_ : IDiscreteStr K}} where

  module _ {σ : Signature} where
    private
      variable k : K
               ks : Vec K n
               -- j : K

    module _ {{_ : ∀{n k} {ks : Vec K (suc n)} -> IDiscreteStr (σ k ks)}} where

    -- private
    --   𝒞 : Category _
    --   𝒞 = ` IdxSet (Maybe K) ℓ₀ `

    -- data SigEdge : (a b : Maybe K) -> 𝒰₀ where
    --   e-arg : ∀ {k} {ks : Vec K (suc n)} -> (i : Fin-R n) -> σ k ks -> SigEdge (just (lookup i ks)) (just k)
    --   e-noarg : ∀{k} -> σ k [] -> SigEdge nothing (just k)

      data SigEdge : (a b : K) -> 𝒰₀ where
        edge : ∀ {k} {ks : Vec K (suc n)} -> (i : Fin-R (suc n)) -> σ k ks -> SigEdge (lookup i ks) k
        fail : ∀{a : K} -> SigEdge a a

      𝑄 : Quiver ⊥
      ⟨ 𝑄 ⟩ = K
      IQuiver.Edge (of 𝑄) = SigEdge
      IQuiver._≈_ (of 𝑄) = _≡_
      IQuiver.IEquivInst (of 𝑄) = IEquiv:Path

      -- compare-sig : ∀{k j₁ j₂ : K} -> {n₁ n₂ : ℕ} -> (s )

      module _ {V : K -> 𝒰₀} where
        lookup-Term : ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> Terms σ V ks -> Term σ V (lookup i ks)
        lookup-Term zero    (t ∷ ts) = t
        lookup-Term (suc i) (t ∷ ts) = lookup-Term i ts

        lookup-Term-try : ∀(n₁ n₂ : ℕ) (ks₁ : Vec K (suc n₁)) (ks₂ : Vec K (suc n₂)) (s₁ : σ k ks₁) (s₂ : σ k ks₂) (i : Fin-R (suc n₂)) (ts : Terms σ V ks₁) -> Maybe (Term σ V (lookup i ks₂))
        lookup-Term-try n₁ n₂ ks₁ ks₂ s₁ s₂ i ts with (n₁ ≟-Str n₂)
        ... | no ¬p = nothing
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = nothing
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = nothing
        ... | yes refl-StrId = right (lookup-Term i ts)

      -- [Theorem]
      -- | The |Monad:TermZ| is recursively accessible.
      interleaved mutual
        RecAccessible:TermZ : IRecAccessible (Monad:TermZ σ)

        -- | First we build the decomposition function:
        decomp : {k : K} {V : K -> 𝒰₀} -> TermZ σ V k -> (∀(j : K) -> SigEdge j k -> Maybe (TermZ σ V j))
        decomp fail _ _ = right fail
        decomp (valid (te t ts)) = {!!}
        decomp (valid (var x)) = {!!}

        -- decomp {k = k} (te {n = n₁} {ks = ks₁} s₁ ts) = right f
        --   where
        --     f : (j : K) → SigEdge j k → Maybe (Term σ V j)
        --     f .(lookup i _) (edge {n = n₂} {ks = ks₂} i s₂) with (n₁ ≟-Str n₂)
        --     ... | no ¬p = nothing
        --     ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        --     ... | no ¬p = nothing
        --     ... | yes refl-StrId with (s₁ ≟-Str s₂)
        --     ... | no ¬p = nothing
        --     ... | yes refl-StrId = right (lookup-Term i ts)
        -- decomp (var x) = left x


        -- | For this we take the following:
        IRecAccessible.Dir RecAccessible:TermZ = of 𝑄
        IRecAccessible.ISet:Dir RecAccessible:TermZ = {!!}
        IRecAccessible.ISet:K RecAccessible:TermZ = {!!}
        IRecAccessible.IDiscreteStr:Dir RecAccessible:TermZ = {!!}
        IRecAccessible.IDiscreteStr:K RecAccessible:TermZ = {!!}
        ⟨ ⟨ IRecAccessible.decompose RecAccessible:TermZ ⟩ ⟩ _ t = decomp t
        of IRecAccessible.decompose RecAccessible:TermZ = {!!}
        IRecAccessible.commutes:decompose RecAccessible:TermZ = {!!}
        IRecAccessible.pts RecAccessible:TermZ = {!!}
        IRecAccessible.a0 RecAccessible:TermZ = {!!}
        IRecAccessible.a0-adsorb RecAccessible:TermZ = {!!}
        IRecAccessible.k-a1 RecAccessible:TermZ = {!!}
        IRecAccessible.a1 RecAccessible:TermZ = {!!}
        IRecAccessible.isDecomposableP RecAccessible:TermZ = {!!}
        IRecAccessible.isPureP RecAccessible:TermZ = {!!}
        IRecAccessible.decideDecompose RecAccessible:TermZ = {!!}
        IRecAccessible.makeDec RecAccessible:TermZ = {!!}
        IRecAccessible.makePure RecAccessible:TermZ = {!!}
        IRecAccessible.isWellfounded::≺ RecAccessible:TermZ = {!!}
        IRecAccessible.cancel-δ RecAccessible:TermZ = {!!}

{-
        decomp : {k : K} -> Term σ V k -> V k +-𝒰 (∀(j : K) -> SigEdge j k -> Maybe (Term σ V j))
        decomp {k = k} (te {n = n₁} {ks = ks₁} s₁ ts) = right f
          where
            f : (j : K) → SigEdge j k → Maybe (Term σ V j)
            f .(lookup i _) (edge {n = n₂} {ks = ks₂} i s₂) with (n₁ ≟-Str n₂)
            ... | no ¬p = nothing
            ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
            ... | no ¬p = nothing
            ... | yes refl-StrId with (s₁ ≟-Str s₂)
            ... | no ¬p = nothing
            ... | yes refl-StrId = right (lookup-Term i ts)
        decomp (var x) = left x

        isMono:decomp : ∀ {k} -> (t s : Term σ V k) -> decomp t ≡-Str decomp s -> t ≡-Str s
        isMono:decomp (te x x₁) (te x₂ x₃) p = {!!}
        isMono:decomp (var x) (var .x) refl-StrId = refl-StrId

      -- decomp nothing none = right (λ j ())
      -- decomp {V = V} (just k) (some (te t ts)) = right (f ts)
      --   where f : Terms σ (V) ks -> (j : K) -> SigEdge j (just k) -> Maybe (Term σ _ j)
      --         f = ?
              -- f xs .(just (lookup i _)) (e-arg i x) = {!!}
              -- f xs .nothing (e-noarg x) = {!!}
              -- f .(just (lookup i _)) (e-arg i x) = {!!}
              -- f .nothing (e-noarg x) = {!!}
      -- decomp (just k) (some (var v)) = left v

      RecAccessible:Term : IRecAccessible (Monad:Term σ)
      IRecAccessible.Dir RecAccessible:Term = of 𝑄
      IRecAccessible.ISet:Dir RecAccessible:Term = {!!}
      ⟨ ⟨ IRecAccessible.decompose RecAccessible:Term ⟩ ⟩ _ = decomp
      of IRecAccessible.decompose RecAccessible:Term = {!!}
      IRecAccessible.IMono:decompose RecAccessible:Term = {!!}
      IRecAccessible.wellfounded RecAccessible:Term = {!!}


-}

