

module Verification.Unification.Target.Presheaves.Functor where

open import Verification.Conventions
open import Verification.Core.Type
-- open import Verification.Core.Algebra
open import Verification.Core.Order
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Functor.Presheaf
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Type.Coproducts
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Instance.TypeProperties
open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Kan.Definition
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Monad.Definition
open import Verification.Unification.RecAccessible
open import Verification.Core.Homotopy.Level



-- {-# BUILTIN REWRITE _≡_ #-}

--------------------------------------------------------------------
-- == The functor to Recursion Modules
-- | Let A, B, C be sets, and let $T$ be a fixed \AD{RecMonad} in this section.

-- Monoid:Path : Quiver 𝑖 -> Monoid (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1)
-- ⟨ Monoid:Path Q ⟩ = Maybe (∑ λ (x : ⟨ Q ⟩) -> ∑ λ (y : ⟨ Q ⟩) -> Edge {{of Q}} x y)
-- IMonoid.𝟷 (of Monoid:Path Q) = {!!}
-- IMonoid._⋅_ (of Monoid:Path Q) = {!!}
-- IMonoid.assoc-⋅ (of Monoid:Path Q) = {!!}
-- IMonoid.unit-l-⋅ (of Monoid:Path Q) = {!!}
-- IMonoid.unit-r-⋅ (of Monoid:Path Q) = {!!}

-- FFF = Functor:Either 𝟙-𝒰

-- module _ {K : 𝒰 𝑖} (E : K -> K -> 𝒰 𝑗) where
--   data Edge₊ : (a b : Maybe K) -> 𝒰 (𝑖 ､ 𝑗) where
--     edge : ∀ {a b} -> E a b -> Edge₊ (just a) (just b)
--     zedge : ∀{a} -> Edge₊ nothing (just a)

instance
  Cast:≡Str : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> Cast (a ≡-Str b) IAnything (a ≡ b)
  Cast.cast Cast:≡Str refl-StrId = refl

≡-Str→≡ : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (a ≡-Str b) -> (a ≡ b)
≡-Str→≡ refl-StrId = refl

≡→≡-Str : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (a ≡ b) -> (a ≡-Str b)
≡→≡-Str = {!!}

cong-Str : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {a b : A} -> (f : A -> B) -> (a ≡-Str b) -> (f a ≡-Str f b)
cong-Str f refl-StrId = refl-StrId

-- right≢left-Str : ∀{a : A}



module _ {K : 𝒰 𝑖} (T' : Monad `(IdxSet K 𝑖)`) {{_ : IRecAccessible T'}} where
  T = ⟨ T' ⟩
  private
    Q : Quiver (𝑖 , 𝑖 , 𝑖)
    ⟨ Q ⟩ = K
    IQuiver.Edge (of Q) = Edge {{Dir}}
    --Maybe (Edge {{Dir}} a b)
    IQuiver._≈_ (of Q) = _≡_
    IQuiver.IEquivInst (of Q) = IEquiv:Path

  𝔇 = (Category:Free Q)

  instance _ = of 𝔇
  instance _ = of Q
  instance _ = of T
  instance _ = of T'



  -- WithTerm : ∀(A : K -> 𝒰 𝑙) -> Maybe K -> 𝒰 𝑙
  -- WithTerm A nothing = `𝟙`
  -- WithTerm A (just x) = A x


  Mod : IdxSet K 𝑖 -> K -> Set 𝑖
  ⟨ Mod X k ⟩ = ∑ λ j -> Hom {{of 𝔇}} k j ×-𝒰 ⟨ ⟨ T ⟩ X ⟩ j
  of Mod X k = {!!}



  private
    data isNormal {A : IdxSet K 𝑖} : ∀{k} -> ⟨ Mod A k ⟩ -> 𝒰 (𝑖) where
      by-id : ∀{k} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ k} -> isNormal (_ , id-Q , a)
      by-nothing : ∀{k j} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ j} -> (e : Edge {{of Q}} k j) -> ⟨ ⟨ decompose ⟩ ⟩ _ a _ e ≡-Str nothing -> isNormal (_ , some (last e) , a)
      by-later : ∀{j k₁ k₂} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ j} -> (p : QPath {{of Q}} k₂ j) -> (e : Edge {{of Q}} k₁ k₂) -> isNormal (_ , some p , a) -> isNormal (_ , some (e ∷ p) , a)

      -- by-[] : ∀{a : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ A ⟩ k} -> isNormal (_ , id-Q , a)
      -- by-eval : ∀{j} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ j} -> {a' : ⟨ A ⟩ j} -> ⟨ ⟨ decompose ⟩ ⟩ _ a ≡-Str left a'
      --            -> (p : Hom k j) -> isNormal (_ , p , right a)

        -- by-[] : ∀{a : ⟨ T ⟩ A} -> (depth a ≡ 0 -> 𝟘-𝒰) -> isNormal ([] , a)
        -- by-depth : ∀{ds} -> ∀{a : ⟨ T ⟩ A} -> depth a ≡ 0 -> isNormal (ds , a)

    instance
      IProp:isNormal : ∀{A : IdxSet K 𝑖} {k} {a : ⟨ Mod A k ⟩} -> IHType 1 (isNormal a)
      IProp:isNormal = {!!}

  Mod-Normal : IdxSet K 𝑖 -> K -> Set 𝑖
  ⟨ Mod-Normal X k ⟩ = ∑ λ (a : ⟨ Mod X k ⟩) -> isNormal a
  of Mod-Normal X k = {!!}

  private
    module _ {X : IdxSet K 𝑖} where
{-
      -- ν-impl-1 : {j : K} {k : K} -> (p : Edge {{of Q}} k j) -> ⟨ ⟨ T ⟩ X ⟩ j -> Maybe (𝟚-𝒰 +-𝒰 (⟨ ⟨ T ⟩ X ⟩ k))
      -- ν-impl-1 nothing x = just (left ₀)
      -- ν-impl-1 (just e) x with ⟨ ⟨ decompose ⟩ ⟩ _ x
      -- ... | left _ = nothing
      -- ... | just xs = just (xs _ e)

      -- ν-impl₁ : {j : K} {k : K} -> (p : QPath {{of Q}} k j) -> 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod-Normal X k ⟩

      ν-impl : {j : K} {k : K} -> (p : QPath {{of Q}} k j) -> 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod X k ⟩
      ν-impl = {!!}
      -- ν-impl p (left x) = _ , id , left ₀
      -- ν-impl (last nothing) (right x) = _ , id , left ₀
      -- ν-impl (last (just e)) (right x) with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x)
      -- ... | left _        = _ , some (last (just e)) , right x
      -- ... | just (xs , _) = _ , id , (xs _ e)
      -- -- ν-impl (nothing ∷ p) (right x) = _ , id , left ₀
      -- ν-impl (e ∷ p) (right x) with ν-impl p (right x)
      -- ... | (_ , some p' , x')       = _ , some (e ∷ p') , x'
      -- ... | (_ , id-Q , left x₁)     = _ , id , left ₀
      -- ... | (_ , id-Q , just x')     with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left _         = _ , some (last (e)) , just x' -- restore old x', with last existing edge e
      -- ν-impl (nothing ∷ p) (just x) | (_ , id-Q , just x')     | just (x'' , _) = _ , id , left ₀
      -- ν-impl (just e ∷ p) (just x)  | (_ , id-Q , just x')     | just (x'' , _) = _ , id-Q , x'' _ e

      ν-impl-isNormal : {j : K} {k : K} -> (p : QPath {{of Q}} k j) -> (x : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j) -> isNormal (ν-impl p x)
      ν-impl-isNormal = {!!}

      -- ν-impl₁ p x = ν-impl p x , ?

-}

      -- ν-impl-2 : {j k : K} -> (p : QPath {{of Q}} (k) (j)) -> ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod X k ⟩


      ν-impl : {j k : K} -> (p : QPath {{of Q}} (k) (j)) -> ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod-Normal X k ⟩
      ν-impl (last e) x with split-+-Str (δ x e)
      ... | left (tt , z) = (_ , some (last e) , x) , by-nothing e z
      ... | just (x' , _) = (_ , id-Q , x') , by-id
      ν-impl (e ∷ p) x with ν-impl p x
      ... | (_ , some p' , x') , N = (_ , some (e ∷ p') , x') , by-later _ _ N
      ... | (_ , id-Q , x') , N with split-+-Str (δ x' e)
      ... | left (tt , z) = (_ , some (last e) , x') , by-nothing e z
      ... | just (x'' , _) = (_ , id-Q , x'') , by-id


      ν : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod-Normal X k ⟩
      ν {.j} (j , id-Q , x) = (_ , id-Q , x) , by-id
      ν {k} (j , some p , x) = ν-impl p x

      ν₁ : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod X k ⟩
      ν₁ x = fst (ν x)


      write : ∀{k j} -> (e : Edge {{of Q}} j k) -> ⟨ Mod X k ⟩ -> ⟨ Mod X j ⟩
      write e (_ , p , x) = (_ , ` e ` ◆ p , x)

{-

      isNormal-ν : ∀{k} -> ∀(x : ⟨ Mod X k ⟩) -> isNormal (ν x)
      isNormal-ν x = {!!}

      ν₁ : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod-Normal X k ⟩
      ν₁ x = ν x , isNormal-ν x

      idempotent-ν : ∀{k} -> ∀{x : ⟨ Mod X k ⟩} -> ν (ν x) ≡ ν x
      idempotent-ν = {!!}




      write-comm-impl-2 : {j k l : K} -> (e : Edge {{of Q}} l k) -> (p : QPath {{of Q}} k j) -> (x : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j) -> (ν-impl (e ∷ p) x ≡-Str write e (ν-impl p x)) +-𝒰 (∑ λ y -> ν-impl p x ≡-Str (_ , id-Q , y))
      write-comm-impl-2 e p (left x) = right (_ , refl)
      write-comm-impl-2 e p (just x) with ν-impl p (right x) | ν-impl-isNormal p (right x)
      ... | .(_ , id-Q , _) | by-[] = right (_ , refl)
      ... | .(_ , id-Q , just _) | by-eval x₁ id-Q = right (_ , refl)
      ... | .(_ , some x₂ , just _) | by-eval x₁ (some x₂) = left refl


-}

      ν-idempotent-impl : ∀{k j} -> (p : QPath {{of Q}} j k) (x : ⟨ ⟨ T ⟩ X ⟩ k) -> isNormal (_ , some p , x) -> ν₁ (_ , some p , x) ≡-Str (_ , some p , x)
      ν-idempotent-impl .(last e) x (by-nothing e P) with split-+-Str (δ x e)
      ... | left _ = refl
      ... | just (_ , Q) = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      ν-idempotent-impl .(e ∷ p) x (by-later p e N) with ν-impl p x | ν-idempotent-impl p x N
      ... | .(_ , some p , x) , snd₁ | refl-StrId = refl

      ν-idempotent : ∀{k} -> ∀(a : ⟨ Mod-Normal X k ⟩) -> ν₁ (fst a) ≡-Str fst a
      ν-idempotent ((_ , (some p) , x) , N) = ν-idempotent-impl p x N
      ν-idempotent ((_ , .id-Q , x) , by-id) = refl

      -- with split-+-Str (δ x e)
      -- ν-idempotent ((_ , .id-Q , x) , by-id) = refl
      -- ν-idempotent ((_ , .(some (last e)) , x) , by-nothing e P) with split-+-Str (δ x e)
      -- ... | left _ = refl
      -- ... | just (_ , Q) = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      -- ν-idempotent ((_ , .(some (e ∷ p)) , x) , by-later p e N) with ν-idempotent ((_ , some p , x) , N)
      -- ... | X = {!!}


      write-comm-impl : {j k l : K} -> (e : Edge {{of Q}} l k) -> (p : QPath {{of Q}} k j) -> (x : ⟨ ⟨ T ⟩ X ⟩ j) -> ν₁ (write e (fst (ν-impl p x))) ≡-Str fst (ν-impl (e ∷ p) x)
      write-comm-impl f (last e) x with split-+-Str (δ x e)
      ... | just (x' , P) with split-+-Str (δ x' f)
      ... | left x₁ = refl
      ... | just x₁ = refl
      write-comm-impl f (last e) x | left (tt , P) with split-+-Str (δ x e)
      ... | left x₁ = refl
      ... | just (_ , Q) = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      write-comm-impl f (e ∷ p) x with ν-impl p x
      ... | (_ , some p' , x') , N = ν-idempotent-impl (f ∷ e ∷ p') x' (by-later _ _ (by-later _ _ N))
      ... | (_ , id-Q , x') , N with split-+-Str (δ x' e)
      ... | left (tt , P) with split-+-Str (δ x' e)
      ... | left _ = refl
      ... | just (_ , Q) = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      write-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | just (x'' , _) with split-+-Str (δ x'' f)
      ... | left _ = refl
      ... | just _ = refl


      -- write-comm-impl e p x with write-comm-impl-2 e p x
      -- ... | left P = {!!}
      -- write-comm-impl e p (left x) | just (fst₁ , P) = refl
      -- write-comm-impl e p (just x) | just (y , P) with ν-impl p (just x) | P
      -- write-comm-impl e p (just x) | just (left x' , P) | .(_ , id-Q , left x') | refl-StrId = refl
      -- write-comm-impl e p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left x₁ = {!!}
      -- write-comm-impl (left x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just x₁ = refl
      -- write-comm-impl (just x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just (x'' , x''p) with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- write-comm-impl (just x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just (x'' , x''p) | left (x''2 , x''2p) with x''2p ⁻¹ ∙ x''p
      -- ... | ()
      -- write-comm-impl (just x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just (x'' , x''p) | right (x''2 , x''2p) with x''2p ⁻¹ ∙ x''p
      -- ... | refl-StrId = refl

{-

      -- write-comm-impl e p (left x) = refl
      -- write-comm-impl e (last nothing) (just x) = refl
      -- write-comm-impl e (last (just x₁)) (just x) = {!!} -- with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x)
      -- write-comm-impl f (e ∷ p) (just x) with ν-impl p (right x) | ν-impl-isNormal p (right x)
      -- ... | _ , some x₁ , just x₂ | Y = {!!}
      -- ... | _ , id-Q , left x₁ | Y = {!!}
      -- ... | _ , id-Q , just x' | Y with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left _ = {!!}
      -- write-comm-impl f (left x₁ ∷ p) (just x) | _ , id-Q , just x' | Y | just x'' = {!!}
      -- write-comm-impl f (just x₁ ∷ p) (just x) | _ , id-Q , just x' | Y | just (x'' , _) = {!!}

      -- ... | _ , id-Q , left x₁ = {!!}
      -- ... | _ , some x₂ , left x₁ = {!!}
      -- ... | _ , p' , just x₁ = {!!}

      -- with ν-impl p (right x) | ν-impl (e ∷ p) (right x)
      -- ... | _ , some x₁ , x' | _ , id-Q , left x₂ = {!!}
      -- ... | _ , some x₁ , x' | _ , id-Q , just x₂ = {!!}
      -- ... | _ , some x₁ , x' | _ , some x₂ , x'2 = {!!}
      -- ... | _ , id-Q , left x' | _ , id-Q , left x₁ = {!!}
      -- ... | _ , id-Q , left x' | _ , id-Q , just x₁ = {!!}
      -- ... | _ , id-Q , left x' | _ , some x₁ , left x₂ = {!!}
      -- ... | _ , id-Q , left x' | _ , some x₁ , just x₂ = {!!}
      -- ... | _ , id-Q , just x' | Z = {!!}


      -- with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left x₁ = {!!}
      -- write-comm-impl f (left x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}
      -- write-comm-impl f (just x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}

      -- write-comm-impl f (e ∷ p) (just x) with ν-impl p (right x)
      -- ... | _ , some x₁ , x' = {!!}
      -- ... | _ , id-Q , left x' = {!!}
      -- ... | _ , id-Q , just x' with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left x₁ = {!!}
      -- write-comm-impl f (left x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}
      -- write-comm-impl f (just x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}


      -- write-comm-impl e p (left x) = refl
      -- write-comm-impl f (last (nothing)) (just x) = refl
      -- write-comm-impl f (last (just x₁)) (just x) with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x)
      -- ... | just _ = refl
      -- ... | left P with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x)
      -- ... | left _ = refl
      -- ... | just Q = {!!} -- 𝟘-elim (left≢right (snd P ⁻¹ ∙ snd Q))
      -- write-comm-impl f (e ∷ p) (just x) = {!!}

-}
      write-comm : ∀{k j} -> (e : Edge {{of Q}} j k) -> (x : ⟨ Mod X k ⟩)-> ν₁ (write e (ν₁ x)) ≡ ν₁ (write e x)
      write-comm e (j , id-Q , x) = refl
      write-comm e (j , some p , x) = ` write-comm-impl e p x `
      -- write-comm e (j , id-Q , x) = refl
      -- write-comm e (j , some p , x) = write-comm-impl e p x
{-
      -- write-comm e (j , p , left x) = refl
      -- write-comm e (j , id-Q , just x) = refl
      -- write-comm e (j , some p , just x) = ?

-}
    module _ {X Y : IdxSet K 𝑖} where
      apply : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> ⟨ Mod X k ⟩ -> ⟨ Mod Y k ⟩
      apply f (_ , p , x) = (_ , p , ⟨ _=<< {{of T'}} f ⟩ _ x)
      -- apply f (_ , p , left x) = (_ , p , left x)
      -- apply f (_ , p , right x) = (_ , p , right (⟨ f =<< ⟩ _ x))


      -- % https://q.uiver.app/?q=WzAsNixbMCwwLCJUWCJdLFswLDEsIlRUWSJdLFswLDIsIlRZIl0sWzEsMCwiRFRYIl0sWzEsMSwiRFRUWSJdLFsxLDIsIkRUWSJdLFswLDMsIlxcZGVsdGEiXSxbMCwxLCJUZiIsMl0sWzMsNCwiRFRmIl0sWzEsMiwiXFxtdSIsMl0sWzIsNSwiXFxkZWx0YSIsMl0sWzQsNSwiRFxcbXUiXV0=
      -- | Here we do the following:
      -- \[\begin{tikzcd}
      -- 	TX & DTX \\
      -- 	TTY & DTTY \\
      -- 	TY & DTY
      -- 	\arrow["\delta", from=1-1, to=1-2]
      -- 	\arrow["Tf"', from=1-1, to=2-1]
      -- 	\arrow["DTf", from=1-2, to=2-2]
      -- 	\arrow["\mu"', from=2-1, to=3-1]
      -- 	\arrow["\delta"', from=3-1, to=3-2]
      -- 	\arrow["D\mu", from=2-2, to=3-2]
      -- \end{tikzcd}\]
      δ-comm : ∀(f : X ⟶ ⟨ T ⟩ Y) -> ∀{j k} -> ∀(e : Edge {{of Q}} k j) (x : ⟨ ⟨ T ⟩ X ⟩ j) -> map-Maybe (⟨ map f ◆ join ⟩ _) (δ x e) ≡ δ (⟨ map f ◆ join ⟩ _ x) e
      δ-comm f e x =
        let P1 : ⟨ decompose ⟩ ◆ map {{of T ◆ Decomp Dir}} f ≣ map f ◆ ⟨ decompose ⟩
            P1 = naturality {{of decompose}} f
            P2 : ⟨ decompose ⟩ ◆ map {{of Decomp Dir}} (⟨ μ T' ⟩ {Y}) ≣ ⟨ μ T' ⟩ ◆ ⟨ decompose ⟩
            P2 = commutes:decompose
            -- P3 : ⟨ decompose ⟩ ◆ map {{of T ◆ Decomp Dir}} f ◆ map {{of Decomp Dir}} (⟨ μ T' ⟩)
            --      ≣ map f ◆ ⟨ μ T' ⟩ ◆ ⟨ decompose ⟩
            -- P3 = {!!}

            P3 : ⟨ decompose ⟩ ◆ map {{of Decomp Dir}} (map {{of T}} f ◆ ⟨ μ T' ⟩)
                 ≣ map f ◆ ⟨ μ T' ⟩ ◆ ⟨ decompose ⟩
            P3 = {!!}
            -- P4 : map-Maybe
            --       (λ a →
            --         ⟨ IMonad.join (of T') ⟩ _ (⟨ IFunctor.map (of ⟨ T' ⟩) f ⟩ _ a))
            --       (δ x e)
            --       ≡
            --       δ (⟨ IMonad.join (of T') ⟩ _ (⟨ IFunctor.map (of ⟨ T' ⟩) f ⟩ _ x))
            --       e
            P4 = funExt⁻¹ (funExt⁻¹ (P3 _ x) _) e
        in P4

      apply-comm-impl : {j k : K} -> (f : X ⟶ ⟨ T ⟩ Y) -> (p : QPath {{of Q}} k j) -> (x : ⟨ ⟨ T ⟩ X ⟩ j) -> ν₁ (apply f (fst (ν-impl p x))) ≡ fst (ν ((_ , some p , ⟨ map f ◆ join ⟩ _ x)))
      apply-comm-impl f (last e) x with (δ-comm f e x) | split-+-Str (δ x e)
      ... | X | left x₁ = refl
      ... | X | just (a , P) with split-+-Str (δ (⟨ map f ◆ join ⟩ _ x) e)
      ... | left (tt , Q) =
        let R : map-Maybe (⟨ map f ◆ join ⟩ _) (just a) ≡ nothing
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ _)) (≡-Str→≡ (P ⁻¹)) ∙ X ∙ ` Q `
        in 𝟘-rec (right≢left R)
      ... | just (b , Q) =
        let R : map-Maybe (⟨ map f ◆ join ⟩ _) (just a) ≡ just b
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ _)) (≡-Str→≡ (P ⁻¹)) ∙ X ∙ ` Q `

        in λ i -> (_ , id-Q , isInjective:right R i)

      -- see 2021-02-20:
      apply-comm-impl f (e ∷ p) x with ν-impl p x | ν-impl p (⟨ map f ◆ join ⟩ _ x) | ≡→≡-Str (apply-comm-impl f p x)
      ... | (_ , some p' , x') , N    | (_ , p'2 , x'2) , N2 | Y with ν-impl p' (⟨ map f ◆ join ⟩ _ x')
      apply-comm-impl f (e ∷ p) x | (_ , some p' , x') , N | (_ , id-Q , x'2) , N2 | refl-StrId | .(_ , id-Q , x'2) , snd₁ = refl
      apply-comm-impl f (e ∷ p) x | (_ , some p' , x') , N | (_ , some x₁ , x'2) , N2 | refl-StrId | .(_ , some x₁ , x'2) , snd₁ = refl

      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(fst (ν (_ , id-Q , _))) , snd₁ | refl-StrId with split-+-Str (δ x' e) | split-+-Str (δ (⟨ map f ◆ join ⟩ _ x') e)
      ... | just (a , P) | left (tt , Q) =
        -- NOTE: here we do the same as in the `last e` case above
        let R : map-Maybe (⟨ map f ◆ join ⟩ _) (just a) ≡ nothing
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ _)) (≡-Str→≡ (P ⁻¹)) ∙ δ-comm f e x' ∙ ` Q `
        in 𝟘-rec (right≢left R)
        -- NOTE: here we do the same as in the `last e` case above
      ... | just (a , P) | just (b , Q) =
        let R : map-Maybe (⟨ map f ◆ join ⟩ _) (just a) ≡ just b
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ _)) (≡-Str→≡ (P ⁻¹)) ∙ δ-comm f e x' ∙ ` Q `
        in λ i -> (_ , id-Q , isInjective:right R i)

      ... | left (tt , Q) | Z with split-+-Str (δ (⟨ map f ◆ join ⟩ _ x') e)
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | just (_ , Z1) | left (_ , Z2) = 𝟘-rec (left≢right `(Z2 ⁻¹ ∙ Z1)`)
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | just (_ , Z1) | just (_ , Z2) = λ i -> (_ , id-Q , isInjective:right R i)
        where R = `(Z2 ⁻¹ ∙ Z1)`
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | left x₁ | left x₂ = refl
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | left (_ , Z1) | just (_ , Z2) = 𝟘-rec (right≢left `(Z2 ⁻¹ ∙ Z1)`)


-- ... | (_ , some p' , x') , N    | (_ , id-Q , x'2) , N2 | Y  = {!!}
      -- ... | (_ , some p' , x') , N    | (_ , some p'2 , x'2) , N2 | Y with ν-impl p' (⟨ map f ◆ join ⟩ _ x')
      -- apply-comm-impl f (e ∷ p) x | (_ , some p' , x') , N | (_ , some p'2 , x'2) , N2 | refl-StrId | .(_ , some p'2 , x'2) , snd₁ = refl


      apply-comm : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> (x : ⟨ Mod X k ⟩) -> ν₁ (apply f (ν₁ x)) ≡ ν₁ (apply f x)
      apply-comm f (_ , id-Q , x) = refl
      apply-comm f (_ , some p , x) = apply-comm-impl f p x
      -- apply-comm f (_ , id-Q , x) = refl
      -- apply-comm f (_ , some x₁ , x) = {!!}

  𝑺 : IdxSet K 𝑖 -> PSh 𝔇 𝑖
  𝑺 X = mirror-Functor (free-Diagram f)
    where f : QuiverHom (Q) (ForgetCategory (` Set 𝑖 ` ᵒᵖ))
          ⟨ f ⟩ k = Mod-Normal X k
          ⟨ IQuiverHom.qmap (of f) e ⟩ (x , _) = ν (write e x)
          of IQuiverHom.qmap (of f) e = record {}


  private
    module _ {X Y : IdxSet K 𝑖} (f : X ⟶ ⟨ T ⟩ Y) where

  {-
      g' : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod Y k ⟩
      g' ((j , p , left a)) = ((j , p , left a)) -- normaliz
      g' ((j , p , just x)) = (j , p , just (⟨ f =<< ⟩ j x))
      -}

      g : ∀(k : K) -> ⟨ 𝑺 X ⟩ k ⟶ ⟨ 𝑺 Y ⟩ k
      ⟨ g k ⟩ (x , xp) = ν (apply f x)


      gp : {a b : K} (e : (Edge {{Dir}} b a)) (x : ⟨ ⟨ 𝑺 X ⟩ a ⟩) →
            ⟨ map {{of 𝑺 Y}} (⩚ e) ⟩ (⟨ g a ⟩ x) ≡
            ⟨ g b ⟩ (⟨ map {{of 𝑺 X}} (⩚ e) ⟩ x)
      gp e ((j , p , x) , pp) = byFirstP P

       where P : ν₁ (write e (ν₁ (apply f (j , p , x))))
                  ≡
                ν₁ (apply f (ν₁ (write e (j , p , x))))
             P = write-comm e (apply f (j , p , x)) ∙ apply-comm f (write e (j , p , x)) ⁻¹

  module _ {X Y : IdxSet K 𝑖} where
    map-𝑺 : (f : X ⟶ ⟨ T ⟩ Y) -> 𝑺 X ⟶ 𝑺 Y
    map-𝑺 f = mirror-Nat (free-Diagram-Natimpl (g f) (λ e x -> gp f e x ⁻¹))

  private
    module _ {X : IdxSet K 𝑖} where
      ι : ∀{k} -> (x : ⟨ ⟨ T ⟩ X ⟩ k) -> ⟨ Mod-Normal X k ⟩
      ι x = (_ , id-Q , x) , by-id

      infixr 40 _↷_
      _↷_ : ∀{k j} -> Hom {{of 𝔇}} j k -> (x : ⟨ Mod-Normal X k ⟩) -> ⟨ Mod-Normal X j ⟩
      _↷_ f x = ⟨ map {{of 𝑺 X}} f ⟩ x

      assoc-↷ : ∀{j k l} -> {f : Hom {{of 𝔇}} l k} -> {g : Hom {{of 𝔇}} k j} -> {x : ⟨ Mod-Normal X j ⟩}
                -> f ↷ g ↷ x ≡ (f ◆ g) ↷ x
      assoc-↷ {f = f} {g = g} {x} = functoriality-◆ {{of 𝑺 X}} {f = g} {g = f} x ⁻¹

      lem-0 : ∀{k} -> (x : ⟨ ⟨ T ⟩ X ⟩ k) -> ` a0 ` ↷ ι x ≡ ι e0
      lem-0 {k = k} x with split-+-Str (δ x a0) | ≡→≡-Str (a0-adsorb x)
      ... | left (_ , P) | Q = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      ... | just (b , P) | Q with P ⁻¹ ∙ Q
      ... | refl-StrId = refl


    module _ {X Y : IdxSet K 𝑖} (α : 𝑺 X ⟶ 𝑺 Y) where
      -- lem-1 : ∀{k : K} -> {} -> ⟨ ⟨ α ⟩ ⟩ (ι {k = k} e0) ≡ ι e0

      module lem-1 {k : K} (x : ⟨ ⟨ T ⟩ X ⟩ k) where
        α' = ⟨ ⟨ α ⟩ {k} ⟩
        P1 : ∀ y -> ` a0 ` ↷ α' (ι y) ≡ α' (ι e0)
        P1 = λ y -> ` a0 ` ↷ α' (ι y) ≡⟨ naturality {{of α}} ` a0 ` (ι y) ⟩
                    α' (` a0 ` ↷ ι y) ≡[ i ]⟨ α' (lem-0 y i) ⟩
                    α' (ι e0)          ∎

        P1-1 : ` a0 ` ↷ α' (ι x) ≡ α' (ι e0)
        P1-1 = P1 x

        P1-2 : (` a0 ` ◆ ` a0 `) ↷ α' (ι x) ≡ α' (ι e0)
        P1-2 = (` a0 ` ◆ ` a0 `) ↷ α' (ι x) ≡⟨ assoc-↷ {f = ` a0 `} {g = ` a0 `} {x = α' (ι x)} ⟩
                ` a0 ` ↷ (` a0 ` ↷ α' (ι x)) ≡[ i ]⟨ ` a0 ` ↷ P1 x i ⟩
                ` a0 ` ↷ α' (ι e0)          ≡⟨ P1 e0 ⟩
                α' (ι e0)                    ∎

        P2 : ` a0 ` ↷ α' (ι x) ≡ (` a0 ` ◆ ` a0 `) ↷ α' (ι x)
        P2 = P1-1 ∙ P1-2 ⁻¹

        proof : ∑ λ y -> ⟨ ⟨ α ⟩ ⟩ (ι x) ≡ ι y
        proof with α' (ι x) | ≡→≡-Str P2
        ... | (_ , id-Q , x') , by-id | _ = _ , refl
        ... | (_ , some p' , x') , N   | Q with ν-impl p' x' | ν-idempotent-impl p' x' N
        ... | .(_ , some p' , x') , N2 | refl-StrId with ν-impl p' x' | ν-idempotent-impl p' x' N2
        proof | (_ , some p' , x') , N | () | .(_ , some p' , x') , N2 | refl-StrId | .(_ , some p' , x') , snd₁ | refl-StrId


  module _ {X Y : IdxSet K 𝑖} where
    map⁻¹-𝑺 : (𝑺 X ⟶ 𝑺 Y) -> (X ⟶ ⟨ T ⟩ Y)
    ⟨ map⁻¹-𝑺 α ⟩ k x = lem-1.proof α (⟨ return ⟩ _ x) .fst



    -- with ⟨ ⟨ f ⟩ ⟩ (ι (⟨ return ⟩ _ x))
    -- ... | a = {!!}

      -- ((_ , id-Q , ⟨ return {{of T'}} ⟩ _ x) , by-id)

    -- ⟨ map⁻¹-𝑺 f ⟩ k x with ⟨ ⟨ f ⟩ ⟩ ((_ , id , right (⟨ return ⟩ _ x)) , by-[])
    -- ... | (_ , q , left y) , _ = {!!}
    -- ... | (_ , id-Q , just y) , _ = y
    -- ... | (_ , some x₁ , just y) , _ = {!!}
    -- of map⁻¹-𝑺 f = record {}
    -- -- (free-Diagram-Natimpl (g f) (λ e x -> gp f e x))

{-



      -- where g : ∀(k : K) -> ⟨ 𝑺 X ⟩ k ⟶ ⟨ 𝑺 Y ⟩ k
      --       ⟨ g k ⟩ ((j , p , left a) , _) = ν ((j , p , left a)) -- ν (j , p , {!!}) -- (j , p ,  ⟨ f =<< ⟩ j x)
      --       ⟨ g k ⟩ ((j , p , just x) , _) = ν (j , p , just (⟨ f =<< ⟩ j x)) -- (j , p ,  ⟨ f =<< ⟩ j x)
      --       of g k = record {}

      --       gp : {a b : K} (e : Maybe (Edge {{Dir}} a b)) (x : ⟨ ⟨ 𝑺 X ⟩ a ⟩) →
      --             ⟨ map {{of 𝑺 Y}} (⩚ e) ⟩ (⟨ g a ⟩ x) ≡
      --             ⟨ g b ⟩ (⟨ map {{of 𝑺 X}} (⩚ e) ⟩ x)
      --       gp e ((j , p , left x) , _) = {!!}
      --       gp e ((j , p , just x) , _) = {!!}


            -- gp2 : {a b : K}
            --         (e : 𝟙-𝒰 +-𝒰 Edge {{Dir}} a b)
            --         (x
            --         : Σ (Σ K (λ j → Σ (Hom {{of 𝔇 ᵒᵖ}} j a) (λ a₁ → 𝟙-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j)))
            --           (isNormal X a)) →
            --         ν
            --         (fst (fst (⟨ g a ⟩ x)) ,
            --         (some (last e)) ◆ (fst (snd (fst (⟨ g a ⟩ x)))) ,
            --         snd (snd (fst (⟨ g a ⟩ x))))
            --         ≡
            --         ⟨ g b ⟩
            --         (ν
            --         (fst (fst x) ,
            --           (some (last e)) ◆ (fst (snd (fst x)))  ,
            --           snd (snd (fst x))))
            -- gp2 = {!!}
    -- ⟨ ⟨ map-𝑺 f ⟩ {x = k} ⟩ ((j , p , x) , _) = ν (j , p ,  ⟨ f =<< ⟩ j x)
    -- of ⟨ map-𝑺 f ⟩ = record {}
    -- INatural.naturality (of map-𝑺 f) = {!!}

-}


  Functor:𝑺 : Functor (` IdxSet K 𝑖 ` ⌄ T') `(PSh 𝔇 𝑖)`
  ⟨ Functor:𝑺 ⟩ X = 𝑺 ⟨ X ⟩
  IFunctor.map (of Functor:𝑺) f = map-𝑺 ⟨ f ⟩
  IFunctor.functoriality-id (of Functor:𝑺) = {!!}
  IFunctor.functoriality-◆ (of Functor:𝑺) = {!!}
  IFunctor.functoriality-≣ (of Functor:𝑺) = {!!}



{-
  𝔇 = Monoid:Free Dir

  private
    Mon : ∀(A : 𝒰 𝑖) -> MonoidModule 𝔇 𝑖
    Mon A = MonoidModule:Free 𝔇 (⟨ T ⟩ A)

  norm' : ⟨ 𝔇 ⟩ -> ⟨ T ⟩ A -> ⟨ Mon A ⟩
  norm' [] a = ([] , a)
  norm' (d ∷ ds) a with ⟨ decompose ⟩ a
  ... | left x = (d ∷ ds , a)
  ... | just x = norm' ds (x d)

  norm : ⟨ Mon A ⟩ -> ⟨ Mon A ⟩
  norm (ds , a) = norm' ds a



  private
    data isNormal : ⟨ Mon A ⟩ -> 𝒰 (𝑖 ⁺) where
       by-[] : ∀{a : ⟨ T ⟩ A} -> (depth a ≡ 0 -> 𝟘-𝒰) -> isNormal ([] , a)
       by-depth : ∀{ds} -> ∀{a : ⟨ T ⟩ A} -> depth a ≡ 0 -> isNormal (ds , a)

    lem::1 : ∀(a : ⟨ Mon A ⟩) -> isNormal a -> norm a ≡ a
    lem::1 ([] , a) P = refl
    lem::1 (d ∷ ds , a) (by-depth P) with ⟨ decompose ⟩ a | strict a
    ... | left a₂ | X = refl
    ... | just a₂ | X =
      let P₂ : depth (a₂ d) < depth a
          P₂ = X d

          P₃ : depth (a₂ d) < 0
          P₃ = transport (λ i -> depth (a₂ d) < P i) P₂

          P₄ : 𝟘-𝒰
          P₄ = P₃ .snd (≤0→≡0 (P₃ .fst))

      in 𝟘-elim P₄

    lem::2 : ∀(ds : ⟨ 𝔇 ⟩) -> (a : ⟨ T ⟩ A) -> isNormal (norm' ds a)
    lem::2 [] a with split-ℕ (depth a)
    ... | left x = by-depth x
    ... | just x = by-[] (λ a≡0 -> zero≢suc (a≡0 ⁻¹ ∙ snd x))
    lem::2 (d ∷ ds) a with ⟨ decompose ⟩ a | strict a
    ... | left x | P = by-depth (transport (λ i -> depth (P (~ i)) ≡ 0) depth/return)
    ... | just x | P = lem::2 ds (x d)

    lem::3 : ∀(a : ⟨ Mon A ⟩) -> norm (norm a) ≡ norm a
    lem::3 a = lem::1 (norm a) (lem::2 (fst a) (snd a))

  -}




