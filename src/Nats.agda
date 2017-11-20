module Nats where

open import Agda.Builtin.Nat public
  renaming (Nat to ℕ; _-_ to _∸_)

infixl 5 _>0
infixl 5 _suc>0

data _>0 : ℕ → Set where
  intro : ∀ n → suc n >0

_suc>0 : ∀ {a} → a >0 → suc a >0
intro n suc>0 = intro (suc n)

_*>0_ : ∀ {a b} → a >0 → b >0 → a * b >0
intro n *>0 intro m = intro (m + n * suc m)
