

module Verification.Unification.RecAccessible where

open import Verification.Conventions
open import Verification.Core.Type
open import Verification.Core.Algebra
open import Verification.Core.Order
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Monad
open import Verification.Core.Category.EpiMono
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.TypeProperties
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Homotopy.Level
open import Verification.Core.Order.Instance.Level
--- open import Verification.Core.Category.Limit
-- open import Verification.Unification.Substitution


--------------------------------------------------------------------
-- == Recursion Monads


module _ {K : 𝒰 𝑖} (T : Functor ` IdxSet K 𝑖 ` ` IdxSet K 𝑖 `) (D : IQuiver K (𝑖 , 𝑖)) where
  Decomp : Functor ` IdxSet K 𝑖 ` ` IdxSet K 𝑖 `
  ⟨ ⟨ Decomp ⟩ X ⟩ k = (⟨ X ⟩ k) +-𝒰 (∀(k₂ : K) -> (e : Edge {{D}} k₂ k) -> Maybe (⟨ ⟨ T ⟩ X ⟩ k₂))
  of ⟨ Decomp ⟩ X = {!!}
  ⟨ IFunctor.map (of Decomp) f ⟩ k (left a) = left (⟨ f ⟩ k a)
  ⟨ IFunctor.map (of Decomp) f ⟩ k (just a) = just (λ k₂ e -> {!!})
  of IFunctor.map (of Decomp) x = record {}
  IFunctor.functoriality-id (of Decomp) = {!!}
  IFunctor.functoriality-◆ (of Decomp) = {!!}
  IFunctor.functoriality-≣ (of Decomp) = {!!}

-- [Definition]
-- | A \textbf{recursion monad} is given by a monad \AB{T}, together with a pointed set \AFd{Direction}
-- and an action of this on any set $\AB{T} A$.
module _ {K : 𝒰 𝑖} (T : Monad ` IdxSet K 𝑖 `) where
  record IRecAccessible : 𝒰 (𝑖 ､ 𝑖 ⁺) where

    -- field depth : ∀{A k} -> ⟨ ⟨ T ⟩ A ⟩ k -> ℕ
    --       depth/return : ∀{A : K -> 𝒰 𝑖} -> {{_ : IIdxSet K A}} -> ∀{k : K} -> ∀{a : A k} -> depth (⟨ return {A = ` A `} ⟩ k a) ≡ 0
    field Dir : IQuiver K (𝑖 , 𝑖)
          {{ISet:Dir}} : ∀{a b : K} -> ISet (Edge a b)

    field decompose : Natural ⟨ T ⟩ (Decomp ⟨ T ⟩ Dir)
          {{IMono:decompose}} : IMono decompose
          wellfounded : WellFounded (λ (a b : K) -> QPath a b)
    --       strict : ∀{A} -> ∀(x : ⟨ T ⟩ A) -> on-Decom T Dir (λ a -> x ≡ return a) (λ a -> depth a < depth x) (⟨ decompose ⟩ x)

  open IRecAccessible {{...}} public

-- //

{-


module _ (T : Functor ` 𝒰 𝑖 ` ` 𝒰 𝑖 `) (D : 𝒰 𝑖) where
  Decom : Functor ` 𝒰 𝑖 ` ` 𝒰 𝑖 `
  ⟨ Decom ⟩ X = X +-𝒰 (D -> ⟨ T ⟩ X)
  IFunctor.map (of Decom) f (left x) = left (f x)
  IFunctor.map (of Decom) f (just x) = right (λ d -> map f (x d))
  IFunctor.functoriality-id (of Decom) = {!!}
  IFunctor.functoriality-◆ (of Decom) = {!!}
  IFunctor.functoriality-≣ (of Decom) = {!!}

  -- data on-Decom {A : 𝒰 𝑖} (P : ⟨ T ⟩ A -> 𝒰 𝑗) : ⟨ Decom ⟩ A -> 𝒰 (𝑖 ､ 𝑗) where
  --   isLeft : ∀{a : A} -> on-Decom P ()

  on-Decom : ∀ {A} -> (A -> 𝒰 (𝑖 ､ 𝑗)) -> (⟨ T ⟩ A -> 𝒰 𝑗) -> ⟨ Decom ⟩ A -> 𝒰 (𝑖 ､ 𝑗)
  on-Decom P Q (left x) = P x
  on-Decom P Q (just x) = ∀ d -> Q (x d)

module _ (T : Functor ` 𝒰 𝑖 ` ` 𝒰 𝑖 `) {{_ : IMonad T}} where
  -- "recursively accessible"
  record IRecAccessible-Monad : 𝒰 (𝑖 ⁺) where

    field depth : ∀{A} -> ⟨ T ⟩ A -> ℕ
          depth/return : ∀{A : 𝒰 𝑖} -> ∀{a : A} -> depth (return a) ≡ 0
    field Dir : 𝒰 𝑖

    field decompose : Natural T (Decom T Dir)
          {{IMono:decompose}} : IMono decompose
          strict : ∀{A} -> ∀(x : ⟨ T ⟩ A) -> on-Decom T Dir (λ a -> x ≡ return a) (λ a -> depth a < depth x) (⟨ decompose ⟩ x)

  open IRecAccessible-Monad {{...}} public

-}


{-
record IRecMonad (T : Functor (⌘ 𝒰₀) (⌘ 𝒰₀)) : 𝒰₁ where
  field {{SetMonadInstance}} : ISetMonad T
        Direction : 𝒰₀
        {{PointedInstance}} : IPointed Direction
        depth : ∀{A} -> ⟨ T ⟩ A -> ℕ
        depth/bind : ∀{A B} -> (a : ⟨ T ⟩ A) -> (f : A -> ⟨ T ⟩ B) -> {n : ℕ} -> depth a ≡ suc n -> ∑ λ m -> depth (a >>= f) ≡ suc m
        go-zero : ∀{A} -> (a : ⟨ T ⟩ A) -> depth a ≡ 0 -> A
        go-zero/id : ∀{A} -> (a : ⟨ T ⟩ A) -> (p : depth a ≡ 0) -> return (go-zero a p) ≡ a
        go-suc : ∀{A} -> (a : ⟨ T ⟩ A) -> {n : ℕ} -> depth a ≡ suc n -> Direction -> ⟨ T ⟩ A
        go-suc/depth : ∀{A} -> (a : ⟨ T ⟩ A) -> {n : ℕ} -> (p : depth a ≡ suc n) -> (d : Direction) -> depth (go-suc a p d) ≤ n
        go-suc/bind : ∀{A B} -> (a : ⟨ T ⟩ A) -> (f : A -> ⟨ T ⟩ B) -> {n : ℕ} -> (p : depth a ≡ suc n) -> (d : Direction) -> go-suc a p d >>= f ≡ go-suc (a >>= f) (depth/bind a f p .snd) d
        cancel-go-suc : ∀{A} -> (a b : ⟨ T ⟩ A) {n m : ℕ} -> (p : depth a ≡ suc n) -> (q : depth b ≡ suc m)
                        -> (∀ d -> go-suc a p d ≡ go-suc b q d) -> a ≡ b
-}
{-
        --- go : ∀ {A} -> Direction -> (T A) -> A +-𝒰 (T A)
        --- go/>>= : ∀{A B x} -> {a a' : ⟨ T ⟩ A} -> (f : A -> ⟨ T ⟩ B) -> go x a ≡ right a' -> go x (a >>= f) ≡ right (a' >>= f)
        --- depth/go-right : ∀{A} -> (a a' : ⟨ T ⟩ A) -> ∀ d -> go d a ≡ right a' -> depth a' <-ℕ depth a
        --- depth-ret : ∀{A} -> {a : ⟨ T ⟩ A} -> depth a ≡ 0 -> ∑ λ (a' : A) -> a ≡ return a'
        --- cancel-go : ∀{A} -> (a b : ⟨ T ⟩ A) -> (∀ d -> go d a ≡ go d b) -> a ≡ b

open IRecMonad {{...}} public

unquoteDecl RecMonad derivationMonad = #struct (quote IRecMonad) "T" RecMonad derivationMonad
-- //

-- [Example]
-- | We show that \AD{Type}, as defined in the last section is a recursion monad.
-- | The set of directions is given by:
data Direction-Type : 𝒰₀ where
  dir-⇒1      : Direction-Type
  dir-⇒2      : Direction-Type
  dir-MyBool  : Direction-Type
  dir-MyNat   : Direction-Type

-- | The depth is simply given by the depth of the AST.
depth-Type : ∀ {A} -> Type A -> ℕ
depth-Type (t ⇒ s) = suc (max-ℕ (depth-Type t) (depth-Type s))
depth-Type MyBool = 1
depth-Type MyNat = 1
depth-Type (var x) = 0

-- | The instance is as follows:
IRecMonad:Type : IRecMonad (⌘ Type)
IRecMonad.SetMonadInstance IRecMonad:Type = IMonad:Type
IRecMonad.Direction IRecMonad:Type = Direction-Type
IPointed.pt (IRecMonad.PointedInstance IRecMonad:Type) = dir-MyBool
IRecMonad.depth IRecMonad:Type = depth-Type
IRecMonad.depth/bind IRecMonad:Type = {!!}
IRecMonad.go-zero IRecMonad:Type = {!!}
IRecMonad.go-zero/id IRecMonad:Type = {!!}
IRecMonad.go-suc IRecMonad:Type = {!!}
IRecMonad.go-suc/depth IRecMonad:Type = {!!}
IRecMonad.go-suc/bind IRecMonad:Type = {!!}
IRecMonad.cancel-go-suc IRecMonad:Type = {!!}

-- //




-}



