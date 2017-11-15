module Nats.Multiply.Assoc where

open import Nats
open import Agda.Builtin.Equality

open import Nats.Multiply.Comm
open import Nats.Multiply.Distrib

------------------------------------------------------------------------
-- internal stuffs

private

  a*1+b=a+a*b : ∀ a b → a * suc b ≡ a + a * b
  a*1+b=a+a*b a b
    rewrite nat-multiply-comm a (suc b)
          | nat-multiply-comm a b
            = refl

  a*/b*c/=/a*b/*c : ∀ a b c → a * b * c ≡ a * (b * c)
  assoc-flip : ∀ a b c → a * (b * c) ≡ a * b * c

  a*/b*c/=/a*b/*c  zero   b c = refl
  a*/b*c/=/a*b/*c (suc a) b c
    rewrite a*/b*c/=/a*b/*c a b c
          | nat-multiply-comm a b
          | nat-multiply-distrib-flip b (b * a) c
          | assoc-flip a b c
          | nat-multiply-comm a b
            = refl

  assoc-flip a b c rewrite a*/b*c/=/a*b/*c a b c = refl

------------------------------------------------------------------------
-- public aliases

nat-multiply-assoc : ∀ a b c → a * b * c ≡ a * (b * c)
nat-multiply-assoc = a*/b*c/=/a*b/*c

nat-multiply-assoc-flip : ∀ a b c → a * (b * c) ≡ a * b * c
nat-multiply-assoc-flip = assoc-flip
