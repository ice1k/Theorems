module Rationals.Properties where

open import Nats
open import Rationals
open import Data.Empty
open import Data.Product
open import Agda.Builtin.Equality

private

  a*b÷b=a : ∀ a b {x} → b >0 →
            a * b ÷ b ⟨ x ⟩ →ℕ ≡ (a , refl)
  a*b÷b=a _ _ _ = refl

  _÷0 : ∀ {a} → ℚ a 0 → ⊥
  (_ ÷ .0 ⟨ _ , () ⟩) ÷0

no-infinity : ∀ {a} → ℚ a 0 → ⊥
no-infinity = _÷0

times-div-id : ∀ a b {x} → b >0 →
               a * b ÷ b ⟨ x ⟩ →ℕ ≡ (a , refl)
times-div-id = a*b÷b=a
