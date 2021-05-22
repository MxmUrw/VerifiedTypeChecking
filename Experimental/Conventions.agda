
module Verification.Experimental.Conventions where

open import Verification.Conventions public
open import Verification.Experimental.Meta.Structure public

_≣_ = StrId

const : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> B -> A -> B
const b _ = b


