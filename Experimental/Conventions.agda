
module Verification.Experimental.Conventions where

open import Verification.Conventions hiding (′_′) public
open import Verification.Experimental.Meta.Structure public

open import Verification.Conventions.Meta.Term

_≣_ = StrId

const : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> B -> A -> B
const b _ = b


isUniverse : Term -> Bool
isUniverse (agda-sort s) = true
isUniverse (def (quote 𝒰) _) = true
isUniverse _ = false


#structureOn-impl : Term -> Term -> TC 𝟙-𝒰
#structureOn-impl value hole = do
    Ty <- inferType hole
    -- Ty <- reduce Ty
    -- value <- normalise value
    let Res = if isUniverse Ty
                 then value
                 else con (quote (′_′)) (arg (arg-info visible (modality relevant quantity-ω)) value ∷ [])
    -- let Fun = 
    unify hole Res

-- macro
callWithQuote : Name -> Term -> TC Term
callWithQuote fun ar = do
  -- ar <- normalise ar
  ar <- quoteTC ar
  return (def fun (varg ar ∷ []))

-- macro
--   #structureOn : Term -> Term -> TC 𝟙-𝒰
--   #structureOn value hole = callWithQuote (quote #structureOn-impl) value >>= unify hole

#structureOn : {A : 𝒰 𝑖} (a : A) -> Term -> TC 𝟙-𝒰
#structureOn a hole = do
  a <- quoteTC a
  #structureOn-impl a hole

SomeStructure : 𝒰₀
SomeStructure = Term -> TC 𝟙-𝒰


    -- unify hole cal

    -- (#callWithQuote #shortName value)
    -- val' <- quoteTC value
    -- unify hole (def (quote #shortName) (varg val' ∷ []))

-- macro
--   #short : Term -> Term -> TC 𝟙-𝒰
--   #short value hole = do
--     val' <- quoteTC value
--     unify hole (def (quote #shortName) (varg val' ∷ []))

-- macro
--   mUNIFY : (𝑖 : 𝔏 ^ 3) -> Term -> TC 𝟙-𝒰
--   mUNIFY 𝑖 hole = do
--     Val <- quoteTC (UnificationProblem 𝑖)
--     let Fun = con (quote (′_′)) (arg (arg-info visible (modality relevant quantity-ω)) Val ∷ [])
--     unify hole Fun
