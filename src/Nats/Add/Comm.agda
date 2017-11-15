module Nats.Add.Comm where

open import Agda.Builtin.Equality
open import Nats

------------------------------------------------------------------------
-- internal stuffs

private

  a+0=0+a : ∀ a → a + 0 ≡ a
  a+0=0+a  zero   = refl
  a+0=0+a (suc a)
    rewrite a+0=0+a a = refl

  ++a+b=a+b++ : ∀ a b → suc (a + b) ≡ a + suc b
  ++a+b=a+b++  zero   b = refl
  ++a+b=a+b++ (suc a) b
    rewrite ++a+b=a+b++ a b = refl

  a+b=b+a : ∀ a b → a + b ≡ b + a
  a+b=b+a a  zero   = a+0=0+a a
  a+b=b+a a (suc b)
    rewrite a+b=b+a b a
          | ++a+b=a+b++ a b
            = refl

------------------------------------------------------------------------
-- public aliases

nat-add-comm : ∀ a b → a + b ≡ b + a
nat-add-comm = a+b=b+a
