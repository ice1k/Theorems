module Ints.Add.Assoc where

open import Ints
open import Nats renaming (suc to nsuc; _+_ to _:+:_)

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

  a+0=a : ∀ a → a + + 0 ≡ a
  a+0=a a rewrite int-add-comm a (+ 0) | 0+a=a a = refl

  z+/b+c/=/z+b/+c : ∀ b c → + 0 + (b + c) ≡ (+ 0 + b) + c
  z+/b+c/=/z+b/+c (+    a  ) (+    b  ) = refl
  z+/b+c/=/z+b/+c (-[1+ a ]) (-[1+ b ]) = refl
  z+/b+c/=/z+b/+c (+    a  ) (-[1+ b ])
    rewrite 0+a=a (a ⊖ nsuc b) = refl
  z+/b+c/=/z+b/+c (-[1+ a ]) (+    b  )
    rewrite 0+a=a (b ⊖ nsuc a) = refl

  a+b=a--b : ∀ a b → a + b ≡ a - (- b)
  a+b=a--b a (+ zero  ) = refl
  a+b=a--b a (+ nsuc n)
    rewrite a+b=a--b a (+ n) = refl
  a+b=a--b a (-[1+ n ]) = refl

  a-b+c=a+c-b : ∀ a b c → a ⊖ b + + c ≡ a :+: c ⊖ b
  a-b+c=a+c-b zero  zero    _ = refl
  a-b+c=a+c-b zero (nsuc _) _ = refl
  a-b+c=a+c-b (nsuc _) zero _ = refl
  a-b+c=a+c-b (nsuc a) (nsuc b) c = a-b+c=a+c-b a b c

  a+/b-c/=a+b-c : ∀ a b c → + a + (b ⊖ c) ≡ a :+: b ⊖ c
  a+/b-c/=a+b-c a b c
    rewrite int-add-comm (+ a) (b ⊖ c)
          | a-b+c=a+c-b b c a
          | nat-add-comm a b
            = refl

  b-c-a=b-/c+a/ : ∀ a b c → b ⊖ c + -[1+ a ] ≡ b ⊖ (nsuc c :+: a)
  b-c-a=b-/c+a/ _ zero    zero    = refl
  b-c-a=b-/c+a/ _ zero    (nsuc _) = refl
  b-c-a=b-/c+a/ _ (nsuc _) zero    = refl
  b-c-a=b-/c+a/ a (nsuc b) (nsuc c) = b-c-a=b-/c+a/ a b c

  -a+/b-c/=b-/a+c/ : ∀ a b c → -[1+ a ] + (b ⊖ c) ≡ b ⊖ (nsuc a :+: c)
  -a+/b-c/=b-/a+c/ a b c
    rewrite int-add-comm -[1+ a ] (b ⊖ c)
          | b-c-a=b-/c+a/ a b c
          | nat-add-comm a c
            = refl

  a+/b+c/=/a+b/+c : ∀ a b c → a + (b + c) ≡ a + b + c
  a+/b+c/=/a+b/+c (+ zero) b c rewrite 0+a=a (b + c) | 0+a=a b = refl
  a+/b+c/=/a+b/+c a (+ zero) c rewrite 0+a=a c | a+0=a a = refl
  a+/b+c/=/a+b/+c a b (+ zero) rewrite a+0=a b | a+0=a (a + b) = refl
  a+/b+c/=/a+b/+c (+ a) (+ b) (+ c)
    rewrite nat-add-assoc a b c = refl
  a+/b+c/=/a+b/+c -[1+ a ] -[1+ b ] (+ nsuc c)
    rewrite -a+/b-c/=b-/a+c/ a c b = refl
  a+/b+c/=/a+b/+c -[1+ a ] (+ nsuc b) -[1+ c ]
    rewrite -a+/b-c/=b-/a+c/ a b c
          | b-c-a=b-/c+a/ c b a
            = refl
  a+/b+c/=/a+b/+c (+ nsuc a) -[1+ b ] -[1+ c ]
    rewrite b-c-a=b-/c+a/ c a b = refl
  a+/b+c/=/a+b/+c (+ nsuc a) -[1+ b ] (+ nsuc c)
    rewrite a-b+c=a+c-b a b (nsuc c)
          | a+/b-c/=a+b-c (nsuc a) c b
          | nat-add-assoc-flip a 1 c
          | nat-add-comm a 1
            = refl
  a+/b+c/=/a+b/+c -[1+ a ] (+ nsuc b) (+ nsuc c)
    rewrite a-b+c=a+c-b b a (nsuc c) = refl
  a+/b+c/=/a+b/+c -[1+ a ] -[1+ b ] -[1+ c ]
    rewrite nat-add-comm a (nsuc (b :+: c))
          | nat-add-comm (b :+: c) a
          | nat-add-assoc a b c
            = refl
  a+/b+c/=/a+b/+c (+ nsuc a) (+ nsuc b) -[1+ c ]
    rewrite a+/b-c/=a+b-c (nsuc a) b c
          | nat-add-assoc-flip a 1 b
          | nat-add-comm a 1
            = refl

  exchanged : ∀ a b c → a + b + c ≡ a + (b + c)
  exchanged a b c rewrite a+/b+c/=/a+b/+c a b c = refl

------------------------------------------------------------------------
-- public aliases

int-add-assoc : ∀ a b c → a + (b + c) ≡ a + b + c
int-add-assoc = a+/b+c/=/a+b/+c

int-add-assoc-flip : ∀ a b c → a + b + c ≡ a + (b + c)
int-add-assoc-flip = exchanged
