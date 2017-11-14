module Ints.Add.Assoc where

open import Data.Integer
open import Data.Nat renaming (suc to nsuc; _+_ to _:+:_)

open import Nats.Add.Assoc
open import Nats.Add.Comm

open import Ints.Add.Comm

open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- internal stuffs

private

  0+a=a : ∀ a → + 0 + a ≡ a
  0+a=a (+    n  ) = refl
  0+a=a (-[1+ n ]) = refl

  -- z+/b+c/=/z+b/+c : ∀ b c → + 0 + (b + c) ≡ (+ 0 + b) + c
  -- z+/b+c/=/z+b/+c (+    a  ) (+    b  ) = refl
  -- z+/b+c/=/z+b/+c (-[1+ a ]) (-[1+ b ]) = refl
  -- z+/b+c/=/z+b/+c (+    a  ) (-[1+ b ])
  --   rewrite 0+a=a (a ⊖ nsuc b) = refl
  -- z+/b+c/=/z+b/+c (-[1+ a ]) (+    b  )
  --   rewrite 0+a=a (b ⊖ nsuc a) = refl

  a-b=a+-b : ∀ a b → a ⊖ b ≡ + a - + b
  a-b=a+-b zero  zero    = refl
  a-b=a+-b zero (nsuc _) = refl
  a-b=a+-b (nsuc a) zero
    rewrite nat-add-comm a 0 = refl
  a-b=a+-b (nsuc a) (nsuc b) = refl

  a+/b+c/=/a+b/+c : ∀ a b c → a + (b + c) ≡ a + b + c
  a+/b+c/=/a+b/+c (+    a  ) (+    b  ) (+    c  )
    rewrite nat-add-assoc a b c = refl
  a+/b+c/=/a+b/+c (+    a  ) (+    b  ) (-[1+ c ]) = {!!}
  a+/b+c/=/a+b/+c (+    a  ) (-[1+ b ]) (+    c  )
    rewrite nat-add-assoc a b c = {!!}
  a+/b+c/=/a+b/+c (+    a  ) (-[1+ b ]) (-[1+ c ])
    rewrite nat-add-assoc a b c = {!!}
  a+/b+c/=/a+b/+c (-[1+ a ]) (+    b  ) (+    c  ) = {!!}
  a+/b+c/=/a+b/+c (-[1+ a ]) (+    b  ) (-[1+ c ])
    rewrite nat-add-comm a c = {!!}
  a+/b+c/=/a+b/+c (-[1+ a ]) (-[1+ b ]) (+    c  ) = {!!}
  a+/b+c/=/a+b/+c (-[1+ a ]) (-[1+ b ]) (-[1+ c ])
    rewrite nat-add-comm a (nsuc (b :+: c))
          | nat-add-comm (b :+: c) a
          | nat-add-assoc a b c
          = refl

------------------------------------------------------------------------
-- public aliases

int-add-assoc : ∀ a b c → a + (b + c) ≡ a + b + c
int-add-assoc = a+/b+c/=/a+b/+c
