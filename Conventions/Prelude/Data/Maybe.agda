
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.Maybe where

open import Verification.Conventions.Proprelude

Maybe : 𝒰 𝑖 -> 𝒰 𝑖
Maybe A = 𝟙-𝒰 +-𝒰 A

pattern just a = right a
pattern nothing = left tt

