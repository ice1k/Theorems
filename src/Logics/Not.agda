module Logics.Not where

open import Relation.Nullary

------------------------------------------------------------------------
-- internal stuffs

private

  a=¬∘¬a : ∀ {ℓ} {A : Set ℓ} → A → ¬ (¬ A)
  a=¬∘¬a a = λ z → z a

------------------------------------------------------------------------
-- public aliases

neg-neg : ∀ {ℓ} {A : Set ℓ} → A → ¬ (¬ A)
neg-neg = a=¬∘¬a
