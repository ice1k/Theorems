module Nats.Add.Assoc where

open import Data.Nat
open import Agda.Builtin.Equality

open import Nats.Add.Comm

------------------------------------------------------------------------
-- internal stuffs

private

  0+/b+c/=/0+b/+c : ∀ b c → 0 + (b + c) ≡ (0 + b) + c
  0+/b+c/=/0+b/+c b c
    rewrite nat-add-comm c 0
          | nat-add-comm b 0
            = refl

  a+/b+c/=/a+b/+c : ∀ a b c → a + b + c ≡ a + (b + c)
  a+/b+c/=/a+b/+c zero    b c
    rewrite 0+/b+c/=/0+b/+c b c
            = refl
  a+/b+c/=/a+b/+c (suc a) b c
    rewrite a+/b+c/=/a+b/+c a b c
            = refl

  assoc-flip : ∀ a b c → a + (b + c) ≡ a + b + c
  assoc-flip a b c
    rewrite a+/b+c/=/a+b/+c a b c = refl

------------------------------------------------------------------------
-- public aliases

nat-add-assoc : ∀ a b c → a + b + c ≡ a + (b + c)
nat-add-assoc = a+/b+c/=/a+b/+c

nat-add-assoc-flip : ∀ a b c → a + (b + c) ≡ a + b + c
nat-add-assoc-flip = assoc-flip
