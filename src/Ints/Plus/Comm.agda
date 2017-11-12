module Ints.Plus.Comm where

open import Data.Integer

open import Nats.Plus.Comm

open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- internal stuffs

private

  a+b=b+a : ∀ a b → a + b ≡ b + a
  a+b=b+a (+    a  ) (+    b  )
    rewrite nat-plus-comm a b = refl
  a+b=b+a (+    a  ) (-[1+ b ])
    rewrite nat-plus-comm a b = refl
  a+b=b+a (-[1+ a ]) (+    b  )
    rewrite nat-plus-comm a b = refl
  a+b=b+a (-[1+ a ]) (-[1+ b ])
    rewrite nat-plus-comm a b = refl

------------------------------------------------------------------------
-- public aliases

int-plus-comm : ∀ a b → a + b ≡ b + a
int-plus-comm = a+b=b+a
