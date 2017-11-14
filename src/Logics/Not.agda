module Logics.Not where

open import Relation.Nullary

------------------------------------------------------------------------
-- internal stuffs

private

  a=¬∘¬a : ∀ {ℓ} {A : Set ℓ} → A → ¬ (¬ A)
  a=¬∘¬a a z = z a

------------------------------------------------------------------------
-- public aliases

not-not : ∀ {ℓ} {A : Set ℓ} → A → ¬ (¬ A)
not-not = a=¬∘¬a
