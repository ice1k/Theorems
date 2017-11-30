module Rationals.Add.Comm where

open import Equality
open import Nats using (_*_; zero; ℕ)
                 renaming (suc to s; _+_ to _:+:_)
open import Rationals
open import Rationals.Properties
open import Nats.Add.Comm
open import Nats.Multiply.Distrib
open import Nats.Multiply.Comm

------------------------------------------------------------------------
-- internal stuffs

private

  a/c+b/c=a*b/c : ∀ a b c → a ÷ c + b ÷ c ≡ (a :+: b) ÷ c
  a/c+b/c=a*b/c a b c
    rewrite (a :+: b) ÷ c ↑ c
          | sym (nat-multiply-distrib a b c)
            = refl

  a+b=b+a : ∀ x y → x + y ≡ y + x
  a+b=b+a (a ÷ c) (b ÷ d)
    rewrite a ÷ c ↑ d
          | b ÷ d ↑ c
          | a/c+b/c=a*b/c (a * d) (b * c) (d * c)
          | nat-add-comm (a * d) (b * c)
          | nat-multiply-comm c d
            = refl

------------------------------------------------------------------------
-- public aliases

rational-add-comm : ∀ x y → x + y ≡ y + x
rational-add-comm = a+b=b+a
