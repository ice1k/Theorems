module Ints.Properties where

open import Ints
open import Equality

------------------------------------------------------------------------
-- internal stuffs

private
  ≡→≡ : ∀ a b → (+ a ≡ + b) → a ≡ b
  ≡→≡ a .a refl = refl

  ≡→≡′ : ∀ a b → (-[1+ a ] ≡ -[1+ b ]) → a ≡ b
  ≡→≡′ a .a refl = refl

  ≡←≡ : ∀ a b → a ≡ b → (+ a ≡ + b)
  ≡←≡ a .a refl = refl

  ≡←≡′ : ∀ a b → a ≡ b → (-[1+ a ] ≡ -[1+ b ])
  ≡←≡′ a .a refl = refl

------------------------------------------------------------------------
-- public aliases

eq-int-to-nat : ∀ a b → (+ a ≡ + b) → a ≡ b
eq-int-to-nat = ≡→≡

eq-neg-int-to-nat : ∀ a b → (-[1+ a ] ≡ -[1+ b ]) → a ≡ b
eq-neg-int-to-nat = ≡→≡′

eq-nat-to-int : ∀ a b → a ≡ b → (+ a ≡ + b)
eq-nat-to-int = ≡←≡

eq-neg-nat-to-int : ∀ a b → a ≡ b → (-[1+ a ] ≡ -[1+ b ])
eq-neg-nat-to-int = ≡←≡′
