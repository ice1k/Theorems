module Logics.Not where

open import Function
open import Relation.Nullary

------------------------------------------------------------------------
-- internal stuffs

private

  a=¬∘¬a : ∀ {a} {A : Set a} → A → ¬ (¬ A)
  a=¬∘¬a a z = z a

  /p→q/→¬/p→¬q/ : ∀ {p q} {P : Set p} {Q : Set q} → (P → Q) → (¬ Q → ¬ P)
  /p→q/→¬/p→¬q/ p→q ¬q p = ¬q $ p→q p

------------------------------------------------------------------------
-- public aliases

not-not : ∀ {ℓ} {A : Set ℓ} → A → ¬ (¬ A)
not-not = a=¬∘¬a

contrapositive : ∀ {p q} {P : Set p} {Q : Set q} → (P → Q) → (¬ Q → ¬ P)
contrapositive = /p→q/→¬/p→¬q/
