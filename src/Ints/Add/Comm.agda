module Ints.Add.Comm where

open import Data.Integer

open import Nats.Add.Comm

open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- internal stuffs

private

  a+b=b+a : ∀ a b → a + b ≡ b + a
  a+b=b+a (+    a  ) (+    b  )
    rewrite nat-add-comm a b = refl
  a+b=b+a (+    a  ) (-[1+ b ])
    rewrite nat-add-comm a b = refl
  a+b=b+a (-[1+ a ]) (+    b  )
    rewrite nat-add-comm a b = refl
  a+b=b+a (-[1+ a ]) (-[1+ b ])
    rewrite nat-add-comm a b = refl

------------------------------------------------------------------------
-- public aliases

int-add-comm : ∀ a b → a + b ≡ b + a
int-add-comm = a+b=b+a
