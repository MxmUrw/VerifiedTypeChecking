
module Verification.Core.Syntax.SignatureZ3 where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Type
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Limit.Kan
-- open import Verification.Unification.RecAccessible


module _ {K : 𝒰₀} where
  -- Symbol : 𝒰₀
  -- Symbol = ∑ λ (n : ℕ) -> K ×-𝒰 (Vec K n)

  Signature : 𝒰₁
  Signature = {n : ℕ} -> K -> Vec K (suc n) -> 𝒰₀

  isInhabited-Sig : Signature -> 𝒰₀
  isInhabited-Sig σ = ∀ k -> ∑ λ n -> ∑ λ (ks : Vec K (suc n)) -> σ k ks

  data TermO (σ : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀
  data TermsO (σ : Signature) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀ where
    [] : TermsO σ V []
    _∷_ : ∀{k} {ks : Vec K n} -> (t : TermO σ V k) -> (ts : TermsO σ V ks) -> TermsO σ V (k ∷ ks)

  data TermO σ V k where
    te : ∀{ks : Vec K (suc n)} -> (s : σ k ks) -> (ts : TermsO σ V ks) -> TermO σ V k
    var : V k -> TermO σ V k
    fail : TermO σ V k

  data Term (σ : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀
  data Terms (σ : Signature) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀ where
    [] : Terms σ V []
    _∷_ : ∀{k} {ks : Vec K n} -> (t : Term σ V k) -> (ts : Terms σ V ks) -> Terms σ V (k ∷ ks)

  -- data isNotFail-Term {σ : Signature} {V : K -> 𝒰₀} : {k : K} -> Term σ V k -> 𝒰₀ where
  data Termᵥ (σ : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀

  -- data isNotFail-Terms {σ : Signature} {V : K -> 𝒰₀} : {n : ℕ} {ks : Vec K n} -> Terms σ V ks -> 𝒰₀
  data Termsᵥ (σ : Signature) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀

  data Term σ V k where
    te : ∀{ks : Vec K (suc n)} -> (s : σ k ks) -> (ts : Termsᵥ σ V ks) -> Term σ V k
    var : V k -> Term σ V k
    fail : Term σ V k

  data Termsᵥ σ V where
    _∷_ : {k : K} -> (Termᵥ σ V k) -> ∀{n} -> {ks : Vec K n} -> (ts : Terms σ V ks) -> Termsᵥ σ V (k ∷ ks)
    fail∷_ : {k : K} -> {ks : Vec K n} -> (ts : Termsᵥ σ V ks) -> Termsᵥ σ V (k ∷ ks)

  data Termᵥ σ V k where
    te : ∀{ks : Vec K (suc n)} -> (s : σ k ks) -> (ts : Termsᵥ σ V ks) -> Termᵥ σ V k
    var : V k -> Termᵥ σ V k


  module _ {σ : Signature} {V : K -> 𝒰₀} where
    forget-Term : ∀{k} -> Termᵥ σ V k -> Term σ V k
    forget-Term (te s ts) = te s ts
    forget-Term (var x) = var x

    forget-Terms : {ks : Vec K n} -> Termsᵥ σ V ks -> Terms σ V ks
    forget-Terms (x ∷ ts) = forget-Term x ∷ ts
    forget-Terms (fail∷ ts) = fail ∷ forget-Terms ts

    split:∷ᵥ : {k : K} -> {t s : Termᵥ σ V k} -> ∀{n} -> {ks : Vec K n} -> {u v : Terms σ V ks}
            -> StrId {A = Termsᵥ σ V (k ∷ ks)} (t ∷ u) (s ∷ v) -> (t ≡-Str s) ×-𝒰 (u ≡-Str v)
    split:∷ᵥ refl-StrId = refl , refl

    split:∷ : {k : K} -> {t s : Term σ V k} -> ∀{n} -> {ks : Vec K n} -> {u v : Terms σ V ks}
            -> StrId {A = Terms σ V (k ∷ ks)} (t ∷ u) (s ∷ v) -> (t ≡-Str s) ×-𝒰 (u ≡-Str v)
    split:∷ refl-StrId = refl , refl

    isInjective:forget-Term : ∀{k} -> {t s : Termᵥ σ V k} -> forget-Term t ≡-Str forget-Term s -> t ≡-Str s
    isInjective:forget-Term {t = te s₁ ts} {te .s₁ .ts} refl-StrId = refl-StrId
    isInjective:forget-Term {t = var x} {var .x} refl-StrId = refl-StrId

    isInjective:forget-Terms : {ks : Vec K n} -> {t s : Termsᵥ σ V ks} -> forget-Terms t ≡-Str forget-Terms s -> t ≡-Str s
    isInjective:forget-Terms {t = x ∷ ts} {x₁ ∷ ts₁} p with split:∷ p
    ... | p1 , refl-StrId with isInjective:forget-Term p1
    ... | refl-StrId = refl
    isInjective:forget-Terms {t = x ∷ ts} {fail∷ s} p with split:∷ p
    isInjective:forget-Terms {suc _} {_ ∷ _} {te s₁ ts₁ ∷ ts} {fail∷ s} p | () , p2
    isInjective:forget-Terms {suc _} {_ ∷ _} {var x ∷ ts} {fail∷ s} p | () , p2
    isInjective:forget-Terms {t = fail∷ t} {x ∷ ts} p with split:∷ p
    isInjective:forget-Terms {suc _} {_ ∷ _} {fail∷ t} {te s ts₁ ∷ ts} p | () , p2
    isInjective:forget-Terms {suc _} {_ ∷ _} {fail∷ t} {var x ∷ ts} p | () , p2
    isInjective:forget-Terms {t = fail∷ t} {fail∷ s} p with split:∷ p
    ... | p1 , p2 with isInjective:forget-Terms p2
    ... | refl-StrId = refl-StrId

  module _ {σ : Signature} {V : K -> 𝒰₀} where
    data isFail-Term {k : K} : (Term σ V k) -> 𝒰₀ where
      fail : isFail-Term fail

    cast::isFail-Term : {k : K} -> {t : Term σ V k} -> isFail-Term t -> t ≡ fail
    cast::isFail-Term fail = refl

    data isFail-Terms : {n : ℕ} {ks : Vec K n} -> (ts : Terms σ V ks) -> 𝒰₀ where
      [] : isFail-Terms []
      _∷_ : ∀{k} -> {t : Term σ V k} -> (isFail-Term t) -> {n : ℕ} {ks : Vec K n} -> {ts : Terms σ V ks} -> isFail-Terms ts -> isFail-Terms (t ∷ ts)

    data _⊏-Terms_ : {k : K} -> ∀{n} -> {ks : Vec K n} -> (t : Term σ V k) -> (ts : Terms σ V ks) -> 𝒰₀ where
      this : {k : K} -> {t : Term σ V k} -> ∀{n} -> {ks : Vec K n} -> {ts : Terms σ V ks} -> t ⊏-Terms (t ∷ ts)
      _∷_ : {k₁ k₂ : K} -> {t₁ : Term σ V k₁} -> (t₂ : Term σ V k₂)-> ∀{n} -> {ks : Vec K n} -> {ts : Terms σ V ks} -> t₁ ⊏-Terms ts -> t₁ ⊏-Terms (t₂ ∷ ts)

    data _⊏-Termsᵥ_ : {k : K} -> ∀{n} -> {ks : Vec K n} -> (t : Term σ V k) -> (ts : Termsᵥ σ V ks) -> 𝒰₀ where
      this : {k : K} -> (t : Termᵥ σ V k) -> (t' : Term σ V k) -> (forget-Term t ≡-Str t') -> ∀{n} -> {ks : Vec K n} -> {ts : Terms σ V ks} -> t' ⊏-Termsᵥ (t ∷ ts)
      older : {k₁ k₂ : K} -> {t₁ : Term σ V k₁} -> (t₂ : Termᵥ σ V k₂) -> ∀{n} -> {ks : Vec K n} -> {ts : Terms σ V ks} -> t₁ ⊏-Terms ts -> t₁ ⊏-Termsᵥ (t₂ ∷ ts)
      fail∷_ : ∀ {k} -> {k₁ : K} -> {t₁ : Term σ V k₁} -> ∀{n} -> {ks : Vec K n} -> {ts : Termsᵥ σ V ks} -> t₁ ⊏-Termsᵥ ts -> t₁ ⊏-Termsᵥ (fail∷_ {k = k} ts)

    data _⊏_ : {k₁ k₂ : K} -> (t₁ : Term σ V k₁) -> (t₂ : Term σ V k₂) -> 𝒰₀ where
      te : {k j : K} -> {t : Term σ V k} -> ∀{n} -> {ks : Vec K (suc n)} -> {s : σ j ks} -> {ts : Termsᵥ σ V ks} -> (t ⊏-Terms (forget-Terms ts)) -> t ⊏ te s (ts)
      fail : ∀{k j : K} -> {t : Term σ V k} -> (t ≢-Str fail) -> fail {k = j} ⊏ t

    data _⊏-TermsO_ : {k : K} -> ∀{n} -> {ks : Vec K n} -> (t : TermO σ V k) -> (ts : TermsO σ V ks) -> 𝒰₀ where
      this : {k : K} -> {t : TermO σ V k} -> ∀{n} -> {ks : Vec K n} -> {ts : TermsO σ V ks} -> t ⊏-TermsO (t ∷ ts)
      _∷_ : {k₁ k₂ : K} -> {t₁ : TermO σ V k₁} -> (t₂ : TermO σ V k₂)-> ∀{n} -> {ks : Vec K n} -> {ts : TermsO σ V ks} -> t₁ ⊏-TermsO ts -> t₁ ⊏-TermsO (t₂ ∷ ts)

    data _⊏O_ : {k₁ k₂ : K} -> (t₁ : TermO σ V k₁) -> (t₂ : TermO σ V k₂) -> 𝒰₀ where
      te : {k : K} -> {t : TermO σ V k} -> ∀{n} -> {ks : Vec K (suc n)} -> {s : σ k ks} -> {ts : TermsO σ V ks} -> (t ⊏-TermsO ts) -> t ⊏O te s (ts)

    _⊏'_ : (t s : ∑ Term σ V) -> 𝒰₀
    _⊏'_ (_ , t) (_ , s) = t ⊏ s

    depth-Term : ∀{k} -> Term σ V k -> ℕ
    depth-Terms : ∀{ks : Vec K n} -> Terms σ V ks -> Vec ℕ n
    depth-Termᵥ : ∀{k} -> Termᵥ σ V k -> ℕ
    depth-Termsᵥ : ∀{ks : Vec K n} -> Termsᵥ σ V ks -> Vec ℕ n

    depth-Termᵥ (te s ts) = suc (⋁ (depth-Termsᵥ ts))
    depth-Termᵥ (var x) = 0

    depth-Termsᵥ (t ∷ ts) = depth-Termᵥ t ∷ depth-Terms ts
    depth-Termsᵥ (fail∷ ts) = 0 ∷ depth-Termsᵥ ts

    depth-Terms [] = []
    depth-Terms (t ∷ ts) = depth-Term t ∷ depth-Terms ts

    depth-Term (te s ts) = suc (⋁ (depth-Termsᵥ ts))
    depth-Term (var x) = 0
    depth-Term fail = 0

    depth-forget : ∀{k} -> (t : Termᵥ σ V k) -> depth-Term (forget-Term t) ≡ depth-Termᵥ t
    depth-forget (te s ts) = refl
    depth-forget (var x) = refl

    depth-⊏-Terms : {k : K} -> ∀{n} -> {ks : Vec K n} -> {t : Term σ V k} -> {ts : Terms σ V ks}
                    -> t ⊏-Terms ts -> depth-Term t ≤ ⋁ (depth-Terms ts)
    depth-⊏-Terms {ts = .(_ ∷ _)} this = ι₀-∨ {A = ℕ}
    depth-⊏-Terms {ts = .(t₂ ∷ _)} (t₂ ∷ x) = trans-≤ {A = ℕ} (depth-⊏-Terms x) (ι₁-∨ {A = ℕ} {a = depth-Term t₂})

    depth-⊏-Termsᵥ : {k : K} -> ∀{n} -> {ks : Vec K n} -> {t : Term σ V k} -> {ts : Termsᵥ σ V ks}
                    -> t ⊏-Terms (forget-Terms ts) -> depth-Term t ≤ ⋁ (depth-Termsᵥ ts)
    depth-⊏-Termsᵥ {ts = t ∷ ts} this = trans-≤ {A = ℕ} (0 , depth-forget t) (ι₀-∨ {A = ℕ})
    depth-⊏-Termsᵥ {ts = x₁ ∷ ts} (.(forget-Term x₁) ∷ x) = trans-≤ {A = ℕ} (depth-⊏-Terms x) (ι₁-max {a = depth-Termᵥ x₁})
    depth-⊏-Termsᵥ {ts = fail∷ ts} this = zero-≤
    depth-⊏-Termsᵥ {ts = fail∷ ts} (.fail ∷ x) = trans-≤ {A = ℕ} (depth-⊏-Termsᵥ x) (ι₁-max {a = 0})


    -- depth-⊏-Termsᵥ {ts = .(t ∷ _)} (this t _ x) = {!!}
    -- depth-⊏-Termsᵥ {ts = .(t₂ ∷ _)} (older t₂ x) = {!!}
    -- depth-⊏-Termsᵥ {ts = .(fail∷ _)} (fail∷ P) = {!!}

    private

      -- lem-10-Terms : ∀{n} {ks : Vec K n} -> (x : Terms σ V ks) -> Acc (_⊏'_) (_ , x)

      lem-10 : ∀{k} -> (x : Term σ V k) -> (n : ℕ) -> (depth-Term x ≤ n) -> Acc (_⊏'_) (_ , x)
      lem-10 (te s ts) zero P = 𝟘-rec (¬-<-zero P)
      lem-10 (te s ts) (suc n) P =
        acc (λ { (k , t') (te x) → lem-10 t' n (trans-≤ {A = ℕ} (depth-⊏-Termsᵥ x) (pred-≤-pred P))
               ;  (fst₁ , .fail) (fail a) → acc (λ { (fst₁ , .fail) (fail x) → 𝟘-rec (x refl)})
               })

      lem-10 (var x) n P = acc (λ { (fst₁ , .fail) (fail a) → acc (λ { (fst₁ , .fail) (fail x) → 𝟘-rec (x refl)})})
      lem-10 fail n P = acc (λ { (fst₁ , .fail) (fail a) → acc (λ { (fst₁ , .fail) (fail x) → 𝟘-rec (x refl)})})
      -- acc (λ {x y -> {!!}})

      -- lem-10 (t) = acc (λ { (k , snd₁) (te (this t .snd₁ x)) → {!!}
      --                     ; (k , snd₁) (te (older t₂ x)) → {!!}
      --                     ; (k , snd₁) (te (fail∷ x)) → {!!}})

      -- lem-10 (te s (fail∷ ts)) = acc (λ { (fst , .fail) (te this) → lem-10 fail
      --                                   ; (fst , snd₁) (te (.fail ∷ x)) → {!!}})
      -- -- acc (λ { (_ , t') (te x) → {!!}})
      -- lem-10 (var x) = acc (λ { y ()})
      -- lem-10 (fail) = acc (λ { y ()})

    isWellfounded::⊏ : WellFounded (λ (x y : ∑ Term σ V) -> x .snd ⊏ y .snd)
    isWellfounded::⊏ (_ , x) = lem-10 x (depth-Term x) refl-≤-ℕ

    {-

    _⊏O'_ : (t s : ∑ TermO σ V) -> 𝒰₀
    _⊏O'_ (_ , t) (_ , s) = t ⊏O s

    private
      -- lem-20-Terms : ∀{n} -> ∀{ks : Vec K n} -> (x : TermsO σ V ks) -> Acc (_)
      -- {-# INLINE lem-20 #-}

      postulate
        use : ∀{A B : 𝒰₀} -> A -> B
      -- use = {!!}
      acc-te : ∀{n}-> ∀{ks : Vec K (suc n)} -> (ts : TermsO σ V ks) -> (∀{k} (t : TermO σ V k)
             -> t ⊏-TermsO ts -> Acc (_⊏O'_) (_ , t)) -> ∀ {j} -> ∀(s : σ j (ks)) -> Acc (_⊏O'_) (_ , te s ts)
      acc-te = {!!}

      lem-20 : ∀{k} -> (x : TermO σ V k) -> Acc (_⊏O'_) (_ , x)

      lem-21 : ∀{n}-> ∀{ks : Vec K n} -> (ts : TermsO σ V ks) -> ∀{k} (t : TermO σ V k) -> t ⊏-TermsO ts -> Acc (_⊏O'_) (_ , t)
      lem-21 .(t ∷ _) t this = lem-20 t
      lem-21 .(t₂ ∷ _) t (t₂ ∷ p) = {!!}
      -- lem-21 .(t ∷ _) t this = 
      -- lem-21 .(t₂ ∷ _) t (t₂ ∷ p) = lem-21 t _ p

      -- lem-20 (te s ts) = acc-te ts (lem-21 ts) s
      lem-20 (te s (t ∷ [])) = use (lem-20 t)
      lem-20 (te s (t ∷ (t₁ ∷ ts))) = {!!}
      lem-20 (var x) = acc (λ { y ()})
      lem-20 fail = acc (λ { y ()})

      {-# INLINE lem-21 #-}
      -}

      -- lem-20 (te s (t ∷ [])) = use f -- acc (λ { (_ , t') (te this) → f})
      --   where f = lem-20 t
      -- lem-20 (te s (t ∷ (t₁ ∷ ts))) = {!!}
      -- -- acc (λ {y (te x) → lem-21 _ ts x})
      -- lem-20 (var x) = acc (λ { y ()})
      -- lem-20 fail = acc (λ { y ()})

      -- lem-20 (te s ts) = acc (λ {y (te x) → lem-21 _ ts x})
      -- lem-20 (var x) = acc (λ { y ()})
      -- lem-20 fail = acc (λ { y ()})



      -- acc (λ { (k , t') (te this) → {!!}
      --                   ; (k , t') (te (t₂ ∷ x)) → {!!}})
      {-
    forget-O-Terms : ∀{n} -> {ks : Vec K n} -> Termsᵥ σ V ks -> TermsO σ V ks
    forget-O-Terms (x ∷ ts) = {!!}
    forget-O-Terms (fail∷ ts) = {!!}

    forget-O-Term : ∀{k} -> Term σ V k -> TermO σ V k
    forget-O-Term (te s ts) = te s (forget-O-Terms ts)
    forget-O-Term (var x) = var x
    forget-O-Term fail = fail

    acc-O : ∀{k} -> ∀(x : Term σ V k) -> Acc _⊏O'_ (_ , forget-O-Term x) -> Acc _⊏'_ (_ , x)
    acc-O (te s ts) A = {!!}
    acc-O (var x) A = {!!}
    acc-O fail A = {!!}

    isWellfounded::⊏O : WellFounded (λ (x y : ∑ TermO σ V) -> x ⊏O' y)
    isWellfounded::⊏O (_ , x) = {!!}
    -}


    -- (_ , te s ts) = {!!}
    -- isWellfounded::⊏ (_ , var x) = {!!}
    -- isWellfounded::⊏ (_ , fail) = {!!}
-- acc (λ {(_ , y) y⊏x -> {!!}})

    fail⊏-Terms : {k : K} -> ∀{n} -> {ks : Vec K n} -> {t : Term σ V k} -> {ts : Terms σ V ks}
                -> t ⊏-Terms ts -> isFail-Terms ts -> isFail-Term t
    fail⊏-Terms this (x ∷ F) = x
    fail⊏-Terms (t₂ ∷ P) (x ∷ F) = fail⊏-Terms P F


    join-Term : {k : K} -> Term σ (Term σ V) k -> Term σ V k
    join-Termᵥ : {k : K} -> Termᵥ σ (Term σ V) k -> Term σ V k

    join-Terms : {ks : Vec K n} -> Terms σ (Term σ V) ks -> Terms σ V ks
    join-Terms [] = []
    join-Terms (t ∷ ts) = join-Term t ∷ join-Terms ts

    join-Termsᵥ : {ks : Vec K n} -> Termsᵥ σ (Term σ V) ks -> Terms σ V ks
    join-Termsᵥ (t ∷ ts) = join-Termᵥ t ∷ join-Terms ts
    join-Termsᵥ (fail∷ ts) = fail ∷ join-Termsᵥ ts

    reduce-Term : ∀{k} -> (t : Term σ V k) -> isFail-Term t +-𝒰 (∑ λ (t' : Termᵥ σ V k) -> forget-Term t' ≡ t)
    reduce-Term (te s ts) = right (te s ts , refl)
    reduce-Term (var x) = right (var x , refl)
    reduce-Term fail = left fail

    reduce-Terms : {ks : Vec K n} -> (ts : Terms σ V ks) -> (isFail-Terms ts) +-𝒰 (∑ λ (ts' : Termsᵥ σ V ks) -> forget-Terms ts' ≡ ts)
    reduce-Terms [] = left []
    reduce-Terms (t ∷ ts) with reduce-Term t
    ... | just (t' , t'P) = right (t' ∷ ts , λ i -> t'P i ∷ ts)
    ... | left fail with reduce-Terms ts
    ... | left (ts'F) = left (fail ∷ ts'F)
    ... | just (ts' , ts'P) = right (fail∷ ts' , λ i -> fail ∷ ts'P i)

    join-te : ∀{k} {ks : Vec K (suc n)} -> σ k ks -> Terms σ V ks -> Term σ V k
    join-te s ts with split-+-Str (reduce-Terms ts)
    ... | left (_ , _) = fail
    ... | just ((ts' , _) , _) = te s ts'

    join-Termᵥ (te s ts) = join-te s (join-Termsᵥ ts)
    join-Termᵥ (var x) = x

    join-Term (te s ts) = join-te s (join-Termsᵥ ts)
    join-Term (var t) = t
    join-Term fail = fail

  module _ {σ : Signature} {V : K -> 𝒰₀} where
    join⊏-Terms : {ks : Vec K n} -> ∀{k} -> {t : Term σ (Term σ V) k} {ts : Terms σ (Term σ V) ks} -> t ⊏-Terms ts -> join-Term t ⊏-Terms join-Terms ts
    join⊏-Terms {t = t} {.(t ∷ _)} this = this
    join⊏-Terms {t = t} {.(t₂ ∷ _)} (t₂ ∷ P) = _ ∷ join⊏-Terms P

    split:join∣forget-Term : ∀{k} -> (t : Termᵥ σ (Term σ V) k) -> join-Termᵥ t ≡ join-Term (forget-Term t)
    split:join∣forget-Term (te s ts) = refl
    split:join∣forget-Term (var x) = refl

    split:join∣forget-Terms : {ks : Vec K n} -> (ts : Termsᵥ σ (Term σ V) ks) -> join-Termsᵥ ts ≡ join-Terms (forget-Terms ts)
    split:join∣forget-Terms (t ∷ ts) i = split:join∣forget-Term t i ∷ join-Terms ts
    split:join∣forget-Terms (fail∷ ts) i = fail ∷ split:join∣forget-Terms ts i


  module _ (σ : Signature) where
    IdxTerm : IdxSet K ℓ₀ -> IdxSet K ℓ₀
    ⟨ IdxTerm V ⟩ = Term σ ⟨ V ⟩
    of (IdxTerm V) = {!!}

  module _ {σ : Signature} where
    instance
      IdxSet:IdxTerm : {A : K -> 𝒰₀} -> {{_ : IIdxSet K A}} -> IIdxSet K (Term σ A)
      IdxSet:IdxTerm {A} {{_}} = of IdxTerm σ ` A `

  -- instance
  --   IdxSet:IdxTerm⇈ : {A : K -> 𝒰₀} -> {{_ : IIdxSet K A}} -> IIdxSet K (⇈ A)
  --   IdxSet:IdxTerm⇈ {A} = of _+-IdxSet_ 𝟙 ` A `
  -- = #openstruct IdxTerm


  module _ {σ : Signature} {V W : K -> 𝒰₀} where
    map-Term : {k : K} -> (∀{k} -> V k -> W k) -> Term σ V k -> Term σ W k
    map-Termᵥ : {k : K} -> (∀{k} -> V k -> W k) -> Termᵥ σ V k -> Termᵥ σ W k
    map-Terms : {ks : Vec K n} -> (∀{k} -> V k -> W k) -> Terms σ V ks -> Terms σ W ks
    map-Termsᵥ : {ks : Vec K n} -> (∀{k} -> V k -> W k) -> Termsᵥ σ V ks -> Termsᵥ σ W ks

    map-Termᵥ f (te s ts) = te s (map-Termsᵥ f ts)
    map-Termᵥ f (var x) = var (f x)

    map-Terms f [] = []
    map-Terms f (t ∷ ts) = map-Term f t ∷ map-Terms f ts

    map-Termsᵥ f (t ∷ ts) = map-Termᵥ f t ∷ map-Terms f ts
    map-Termsᵥ f (fail∷ ts) = fail∷ map-Termsᵥ f ts

    map-Term f (te s ts) = te s (map-Termsᵥ f ts)
    map-Term f (var x) = var (f x)
    map-Term f fail = fail

    commutes:map∣forget-Term : ∀{k} -> (f : ∀{k} -> V k -> W k) -> (t : Termᵥ σ V k) -> map-Term f (forget-Term t) ≡ (forget-Term (map-Termᵥ f t))
    commutes:map∣forget-Term f (te s ts) = refl
    commutes:map∣forget-Term f (var x) = refl

    commutes:map∣forget-Terms : {ks : Vec K n} -> (f : ∀{k} -> V k -> W k) -> (ts : Termsᵥ σ V ks) -> map-Terms f (forget-Terms ts) ≡ (forget-Terms (map-Termsᵥ f ts))
    commutes:map∣forget-Terms f (x ∷ ts) i = commutes:map∣forget-Term f x i ∷ map-Terms f ts
    commutes:map∣forget-Terms f (fail∷ ts) i = fail ∷ commutes:map∣forget-Terms f ts i

    map⊏-Terms : {ks : Vec K n} -> (f : ∀{k} -> V k -> W k) -> ∀{k} -> {t : Term σ V k} {ts : Terms σ V ks} -> t ⊏-Terms ts -> map-Term f t ⊏-Terms map-Terms f ts
    map⊏-Terms f {k} {t} {.(t ∷ _)} this = this
    map⊏-Terms f {k} {t} {.(t₂ ∷ _)} (t₂ ∷ P) = _ ∷ map⊏-Terms f P

  private
    𝒞 : Category _
    𝒞 = Category:IdxSet K ℓ₀

  module _ (σ : Signature) where
    Functor:Term : Functor 𝒞 𝒞
    ⟨ Functor:Term ⟩ X = IdxTerm σ X
    -- ⟨ ⟨ Functor:Term ⟩ X ⟩ = Term σ ⟨ X ⟩
    -- IIdxSet.ISet:this (of ⟨ Functor:Term ⟩ z) = {!!}
    ⟨ IFunctor.map (of Functor:Term) f ⟩ = map-Term ⟨ f ⟩
    IFunctor.functoriality-id (of Functor:Term) = {!!}
    IFunctor.functoriality-◆ (of Functor:Term) = {!!}
    IFunctor.functoriality-≣ (of Functor:Term) = {!!}

    Monad:Term : Monad 𝒞
    ⟨ Monad:Term ⟩ = Functor:Term
    ⟨ IMonad.return (of Monad:Term) ⟩ x = (var x)
    ⟨ IMonad.join (of Monad:Term) ⟩ = join-Term
    IMonad.INatural:return (of Monad:Term) = {!!}
    IMonad.INatural:join (of Monad:Term) = {!!}
    IMonad.unit-l-join (of Monad:Term) = {!!}
    IMonad.unit-r-join (of Monad:Term) = {!!}
    IMonad.assoc-join (of Monad:Term) = {!!}

{-

    Functor:TermZ2 = Functor:EitherT 𝟙 (Monad:Term)
    Monad:TermZ2 = Monad:EitherT 𝟙 (Monad:Term)

    TermZ2 : (V : K -> 𝒰₀) -> K -> 𝒰₀
    TermZ2 V k = Term σ (⇈ V) k

    IdxTermZ2 : (V : IdxSet K ℓ₀) -> IdxSet K ℓ₀
    IdxTermZ2 V = IdxTerm σ (𝟙 + V)

    TermsZ2 : (V : K -> 𝒰₀) -> (Vec K n) -> 𝒰₀
    TermsZ2 V ks = Terms σ (⇈ V) ks

  module _ {σ : Signature} {V W : IdxSet K ℓ₀} where
    map-TermZ2 : {k : K} -> (V ⟶ W) -> TermZ2 σ ⟨ V ⟩ k -> TermZ2 σ ⟨ W ⟩ k
    map-TermZ2 {k} f = ⟨ map {{of Functor:TermZ2 σ}} f ⟩ {k}

    map-TermsZ2 : {ks : Vec K n} -> (V ⟶ W) -> TermsZ2 σ ⟨ V ⟩ ks -> TermsZ2 σ ⟨ W ⟩ ks
    map-TermsZ2 f = map-Terms (⟨ map-+-r {c = 𝟙} f ⟩ {_})

  module _ {σ : Signature} {V : IdxSet K ℓ₀} where
    join-TermZ2 : {k : K} -> TermZ2 σ (TermZ2 σ ⟨ V ⟩) k -> TermZ2 σ ⟨ V ⟩ k
    join-TermZ2 {k} x = ⟨ join {{of Monad:TermZ2 σ}} {A = V} ⟩ {k} x
-}
