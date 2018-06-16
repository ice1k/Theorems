module Nats.Add.Assoc where

open import Equality
open import Nats
open import Function

------------------------------------------------------------------------
-- internal stuffs

private

  a+/b+c/=/a+b/+c : ∀ a b c → a + b + c ≡ a + (b + c)
  a+/b+c/=/a+b/+c  zero   b c = refl
  a+/b+c/=/a+b/+c (suc a) b c = cong suc $ a+/b+c/=/a+b/+c a b c

------------------------------------------------------------------------
-- public aliases

nat-add-assoc : ∀ a b c → a + b + c ≡ a + (b + c)
nat-add-assoc = a+/b+c/=/a+b/+c

