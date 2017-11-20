module Nats where

open import Agda.Builtin.Nat public
  renaming (Nat to ℕ; _-_ to _∸_)

infixl 5 _>0

data _>0 : ℕ → Set where
  intro : ∀ n → suc n >0
