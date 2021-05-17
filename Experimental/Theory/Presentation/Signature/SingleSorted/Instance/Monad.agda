
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
    isMonad:TermF : isMonad ′ TermF (𝑖 , 𝑖) σ ′
    isMonad.pure isMonad:TermF = {!!}
    isMonad.join isMonad:TermF = {!!}
    isMonad.isNatural:pure isMonad:TermF = {!!}
    isMonad.isNatural:join isMonad:TermF = {!!}
    isMonad.unit-l-join isMonad:TermF = {!!}
    isMonad.unit-r-join isMonad:TermF = {!!}
    isMonad.assoc-join isMonad:TermF = {!!}



