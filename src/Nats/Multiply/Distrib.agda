module Nats.Multiply.Distrib where

open import Nats
open import Equality
open import Function

open import Nats.Multiply.Comm
open import Nats.Add.Assoc
open import Nats.Add.Comm

------------------------------------------------------------------------
-- internal stuffs

private

  a*1+b=a+a*b : ∀ a b → a * suc b ≡ a + a * b
  a*1+b=a+a*b a b
    rewrite nat-multiply-comm a $ suc b
          | nat-multiply-comm a b
            = refl

  a*c+b*c=/a+b/*c : ∀ a b c → a * c + b * c ≡ (a + b) * c
  a*c+b*c=/a+b/*c a b    zero
    rewrite nat-multiply-comm a 0
          | nat-multiply-comm b 0
          | nat-multiply-comm (a + b) 0
            = refl
  a*c+b*c=/a+b/*c a b sc@(suc c)
    rewrite nat-add-comm a b
          | a*1+b=a+a*b a c
          | nat-add-assoc a (a * c) (b * sc)
          | nat-add-comm a $ a * c + b * sc
          | a*1+b=a+a*b b c
          | nat-multiply-comm (b + a) sc
          | nat-add-assoc b a $ c * (b + a)
          | nat-add-comm a $ c * (b + a)
          | sym $ nat-add-assoc b (c * (b + a)) a
          | nat-multiply-comm c $ b + a
          | sym $ a*c+b*c=/a+b/*c b a c
          | sym $ nat-add-assoc (a * c) b (b * c)
          | nat-add-comm (b * c) (a * c)
          | sym $ nat-add-assoc b (b * c) (a * c)
          | sym $ nat-add-assoc b (a * c) (b * c)
          | nat-add-comm b $ a * c
            = refl

------------------------------------------------------------------------
-- public aliases

nat-multiply-distrib : ∀ a b c → a * c + b * c ≡ (a + b) * c
nat-multiply-distrib = a*c+b*c=/a+b/*c

