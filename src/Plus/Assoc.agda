module Plus.Assoc where

open import Data.Nat
open import Agda.Builtin.Equality

open import Plus.Comm

------------------------------------------------------------------------
-- internal stuffs

private

  0+/b+c/=/0+b/+c : ∀ b c → 0 + (b + c) ≡ (0 + b) + c
  0+/b+c/=/0+b/+c b c
    rewrite plus-comm c 0
          | plus-comm b 0
            = refl

  a+/b+c/=/a+b/+c : ∀ a b c → a + (b + c) ≡ (a + b) + c
  a+/b+c/=/a+b/+c zero    b c
    rewrite 0+/b+c/=/0+b/+c b c
            = refl
  a+/b+c/=/a+b/+c (suc a) b c
    rewrite a+/b+c/=/a+b/+c a b c
            = refl

------------------------------------------------------------------------
-- public aliases

plus-assoc = a+/b+c/=/a+b/+c

