module Ints.Add.Invert where

open import Ints
open import Ints.Properties
open import Ints.Add.Comm
open import Nats.Add.Invert

open import Data.Empty

open import Equality
open import Function

------------------------------------------------------------------------
-- internal stuffs

private

  nat→int : ∀ a b → (+ a + + a ≡ + b + + b) → (a :+: a ≡ b :+: b)
  nat→int a b ev rewrite eq-int-to-nat (a :+: a) (b :+: b) ev = refl

  nat→int′ : ∀ a b → (-[1+ nsuc (a :+: a) ] ≡ -[1+ nsuc (b :+: b)]) → (+ a + + a ≡ + b + + b)
  nat→int′ a b ev
    rewrite nat-add-invert a b
              $ nat-add-invert-1 (a :+: a) (b :+: b)
              $ eq-neg-int-to-nat (nsuc $ a :+: a) (nsuc $ b :+: b) ev = refl

  impossible : ∀ a b → (+ a + + a ≡ -[1+ b ] + -[1+ b ]) → ⊥
  impossible a b ()

  +-invert : ∀ a b → (a + a ≡ b + b) → a ≡ b
  +-invert (+   a ) (+   b ) ev
    rewrite nat-add-invert a b $ nat→int a b ev = refl
  +-invert (+   a ) -[1+ b ] ev = ⊥-elim $ impossible a b ev
  +-invert -[1+ a ] (+   b ) ev = ⊥-elim $ impossible b a $ sym ev
  +-invert -[1+ a ] -[1+ b ] ev
    rewrite nat-add-invert a b $ nat→int a b $ nat→int′ a b ev = refl

------------------------------------------------------------------------
-- public aliases

int-add-invert : ∀ a b → (a + a ≡ b + b) → a ≡ b
int-add-invert = +-invert

