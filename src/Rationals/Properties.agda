module Rationals.Properties where

open import Nats
open import Rationals
open import Data.Empty
open import Data.Product
open import Equality

------------------------------------------------------------------------
-- internal stuffs

private

  a*b÷b=a : ∀ a b → a * b ÷ b →ℕ ≡ (a , refl)
  a*b÷b=a _ _ = refl

------------------------------------------------------------------------
-- public aliases

times-div-id : ∀ a b → a * b ÷ b →ℕ ≡ (a , refl)
times-div-id = a*b÷b=a
