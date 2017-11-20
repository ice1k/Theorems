module Nats.Multiply.Comm where

open import Nats
open import Equality

open import Nats.Add.Comm
open import Nats.Add.Assoc

------------------------------------------------------------------------
-- internal stuffs

private

  a*0=0*a : ∀ a → a * 0 ≡ 0
  a*0=0*a  zero   = refl
  a*0=0*a (suc a) = a*0=0*a a

  a+a*b=a*++b : ∀ a b → a + a * b ≡ a * suc b
  a+a*b=a*++b  zero   _ = refl
  a+a*b=a*++b (suc a) b
    rewrite nat-add-comm b (a * suc b)
          | nat-add-comm b (a * b)
          | nat-add-assoc-flip a (a * b) b
          | a+a*b=a*++b a b
            = refl

  a*b=b*a : ∀ a b → a * b ≡ b * a
  a*b=b*a  zero   b
    rewrite a*0=0*a b = refl
  a*b=b*a (suc a) b
    rewrite a*b=b*a a b
          | a+a*b=a*++b b a
            = refl

------------------------------------------------------------------------
-- public aliases

nat-multiply-comm : ∀ a b → a * b ≡ b * a
nat-multiply-comm = a*b=b*a
