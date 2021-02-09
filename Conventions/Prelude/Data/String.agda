
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.String where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes

open import Agda.Builtin.Char

instance
  IBootMonoid:String : IBootMonoid String
  IBootMonoid.mempty IBootMonoid:String = ""
  IBootMonoid._<>_ IBootMonoid:String = primStringAppend

  IShow:String : IShow String
  IShow.show IShow:String s = s

  IBootEq:String : IBootEq String
  IBootEq._≟_ IBootEq:String = primStringEquality

  IBootEq:Char : IBootEq Char
  IBootEq._≟_ IBootEq:Char = primCharEquality

