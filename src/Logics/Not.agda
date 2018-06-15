module Logics.Not where

open import Function
open import Relation.Nullary

------------------------------------------------------------------------
-- internal stuffs

private

  a=¬∘¬a : ∀ {ℓ} {A : Set ℓ} → A → ¬ (¬ A)
  a=¬∘¬a a z = z a

  /p→q/→¬/p→¬q/ : ∀ {ℓ₀ ℓ₁} {P : Set ℓ₀} {Q : Set ℓ₁} → (P → Q) → (¬ Q → ¬ P)
  /p→q/→¬/p→¬q/ p→q ¬q p = ¬q $ p→q p

------------------------------------------------------------------------
-- public aliases

not-not : ∀ {ℓ} {A : Set ℓ} → A → ¬ (¬ A)
not-not = a=¬∘¬a

contrapositive : ∀ {ℓ₀ ℓ₁} {P : Set ℓ₀} {Q : Set ℓ₁} → (P → Q) → (¬ Q → ¬ P)
contrapositive = /p→q/→¬/p→¬q/
