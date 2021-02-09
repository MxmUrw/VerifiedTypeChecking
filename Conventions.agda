
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions where

open import Verification.Conventions.Prelude hiding (𝑖 ; 𝑗 ; 𝑘 ; 𝑙) public
open import Verification.Conventions.Meta public

variable
  n-𝑖𝑖 n-𝑗𝑗 n-𝑘𝑘 n-𝑙𝑙 : ℕ
  𝑖 : 𝔏 ^-𝒰 n-𝑖𝑖
  𝑗 : 𝔏 ^-𝒰 (n-𝑗𝑗)
  𝑘 : 𝔏 ^-𝒰 (n-𝑘𝑘)
  𝑙 : 𝔏 ^-𝒰 (n-𝑙𝑙)
