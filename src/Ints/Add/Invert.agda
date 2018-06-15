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
  nat→int a b = eq-int-to-nat (a :+: a) (b :+: b)

  nat→int′ : ∀ a b → (-[1+ nsuc (a :+: a) ] ≡ -[1+ nsuc (b :+: b)]) → a ≡ b
  nat→int′ a b ev
    = nat-add-invert a b
              $ nat-add-invert-1 (a :+: a) (b :+: b)
              $ eq-neg-int-to-nat (nsuc $ a :+: a) (nsuc $ b :+: b) ev

  impossible : ∀ a b → (+ a + + a ≡ -[1+ b ] + -[1+ b ]) → ⊥
  impossible a b ()

  +-invert : ∀ a b → (a + a ≡ b + b) → a ≡ b
  +-invert (+   a ) (+   b ) = eq-nat-to-int a b ∘ nat-add-invert a b ∘ nat→int a b
  +-invert (+   a ) -[1+ b ] = ⊥-elim ∘ impossible a b
  +-invert -[1+ a ] (+   b ) = ⊥-elim ∘ impossible b a ∘ sym
  +-invert -[1+ a ] -[1+ b ] = eq-neg-nat-to-int a b ∘ nat→int′ a b

------------------------------------------------------------------------
-- public aliases

int-add-invert : ∀ a b → (a + a ≡ b + b) → a ≡ b
int-add-invert = +-invert

