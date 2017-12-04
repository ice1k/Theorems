module Rationals.Multiply.Comm where

open import Equality
open import Rationals
open import Nats.Multiply.Comm

------------------------------------------------------------------------
-- internal stuffs

private

  a*b=b*a : ∀ x y → x * y ≡ y * x
  a*b=b*a (a ÷ c) (b ÷ d)
    rewrite nat-multiply-comm a b
          | nat-multiply-comm c d
            = refl

------------------------------------------------------------------------
-- public aliases

rational-multiply-comm : ∀ x y → x * y ≡ y * x
rational-multiply-comm = a*b=b*a
