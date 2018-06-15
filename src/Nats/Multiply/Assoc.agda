module Nats.Multiply.Assoc where

open import Nats
open import Equality
open import Function

open import Nats.Multiply.Comm
open import Nats.Multiply.Distrib

------------------------------------------------------------------------
-- internal stuffs

private

  a*1+b=a+a*b : ∀ a b → a * suc b ≡ a + a * b
  a*1+b=a+a*b a b
    rewrite nat-multiply-comm a $ suc b
          | nat-multiply-comm a b
            = refl

  a*/b*c/=/a*b/*c : ∀ a b c → a * b * c ≡ a * (b * c)
  a*/b*c/=/a*b/*c  zero   b c = refl
  a*/b*c/=/a*b/*c (suc a) b c
    rewrite a*/b*c/=/a*b/*c a b c
          | nat-multiply-comm a b
          | sym $ nat-multiply-distrib b (b * a) c
          | sym $ a*/b*c/=/a*b/*c a b c
          | nat-multiply-comm a b
            = refl

------------------------------------------------------------------------
-- public aliases

nat-multiply-assoc : ∀ a b c → a * b * c ≡ a * (b * c)
nat-multiply-assoc = a*/b*c/=/a*b/*c
