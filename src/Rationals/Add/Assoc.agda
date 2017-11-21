module Rationals.Add.Assoc where

open import Equality
open import Nats using (_*_; zero; ℕ)
                 renaming (suc to s; _+_ to _:+:_)
open import Rationals
open import Rationals.Properties
open import Nats.Add.Comm
open import Nats.Add.Assoc
open import Nats.Multiply.Distrib
open import Nats.Multiply.Assoc
open import Nats.Multiply.Comm

------------------------------------------------------------------------
-- internal stuffs

private

  a+b+c=a+/b+c/ : ∀ a b c → a + (b + c) ≡ (a + b) + c
  a+b+c=a+/b+c/ (ax ÷ ay) (bx ÷ by) (cx ÷ cy)
    rewrite ax ÷ ay ↑ (by * cy)
          | bx ÷ by ↑ (ay * cy)
          | cx ÷ cy ↑ (ay * by)
          | nat-multiply-assoc ay by cy
          | nat-multiply-distrib-flip (bx * cy) (cx * by) ay
          | nat-multiply-distrib-flip (ax * by) (bx * ay) cy
          | nat-add-assoc-flip (ax * (by * cy)) (bx * cy * ay) (cx * by * ay)
          | nat-multiply-assoc ax by cy
          | nat-multiply-comm ay by
          | nat-multiply-assoc cx by ay
          | nat-multiply-assoc bx cy ay
          | nat-multiply-assoc bx ay cy
          | nat-multiply-comm cy ay
            = refl

  assoc-flip : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc-flip a b c rewrite a+b+c=a+/b+c/ a b c = refl

rational-add-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
rational-add-assoc = a+b+c=a+/b+c/

rational-add-assoc-flip : ∀ a b c → (a + b) + c ≡ a + (b + c)
rational-add-assoc-flip = assoc-flip
