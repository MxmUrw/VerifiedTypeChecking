
module Verification.Experimental.Category.Standard.Monad.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Standard.Category.Definition
open import Verification.Experimental.Category.Standard.Functor.Definition
open import Verification.Experimental.Category.Standard.Functor.Instance.Category
open import Verification.Experimental.Category.Standard.Natural.Definition
open import Verification.Experimental.Category.Standard.Category.Instance.Category


-- module _ {𝒞 : Category 𝑖} where
--   record hasPure (F : Functor 𝒞 𝒞) : 𝒰 (⨆ 𝑖) where
--     field η : Natural ⟨ id ⟩ F
--     pure : ∀{a} -> a ⟶ ⟨ F ⟩ a
--     pure = ⟨ η ⟩



-- In this section we define monads.
-- | Let [..] be a category.
module _ {𝒞 : Category 𝑖} where
-- [Definition]
-- | A functor |F : 𝒞 ⟶ 𝒞| is a monad,
  record isMonad (F : Functor 𝒞 𝒞) : 𝒰 (⨆ 𝑖) where
--  | if the following additional data is given:

-- | - Two maps |return| and |join|:
    field return  : ∀{A} -> A ⟶ (⟨ F ⟩ A)
          join    : ∀{A} -> (⟨ F ◆-Cat F ⟩ A) ⟶ (⟨ F ⟩ A)
-- | - Proofs that they are natural:
          {{isNatural:return}}  : isNatural ⟨ id ⟩ (F) return
          {{isNatural:join}}    : isNatural (F ◆-Cat F) (F) join
-- | - And behave monoidal.
          -- unit-l-join  : ∀{A : ⟨ 𝒞 ⟩} -> return ◆ join ∼ id {a = ⟨ F ⟩ A}
          -- unit-r-join  : ∀{A : ⟨ 𝒞 ⟩} -> map return ◆ join ∼ id {a = ⟨ F ⟩ A}
          -- assoc-join   : ∀{A : ⟨ 𝒞 ⟩} -> join ◆ join ∼ (map join) ◆ join {A = A}
  open isMonad {{...}} public
-- //

-- unquoteDecl Monad monad = #struct "Mnd" (quote IMonad) "F" Monad monad
