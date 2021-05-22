
module Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Instance.Monad where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Definition
open import Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Instance.Setoid
open import Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Instance.Functor


module _ {σ : Signature} where
  instance
    isMonad:Term : isMonad (𝑇𝑒𝑟𝑚 {𝑖} σ)
    isMonad.pure isMonad:Term = {!!}
    isMonad.join isMonad:Term = {!!}
    isMonad.isNatural:pure isMonad:Term = {!!}
    isMonad.isNatural:join isMonad:Term = {!!}
    isMonad.unit-l-join isMonad:Term = {!!}
    isMonad.unit-r-join isMonad:Term = {!!}
    isMonad.assoc-join isMonad:Term = {!!}



