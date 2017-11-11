module Logics.Or where

open import Logics.And

------------------------------------------------------------------------
-- definitions

data _∨_ (P Q : Set) : Set where
  ∨-intro₀ : P → P ∨ Q
  ∨-intro₁ : Q → P ∨ Q

------------------------------------------------------------------------
-- internal stuffs

private

  p→r+q→r+p∨q=r : ∀ {P Q n} {R : Set n} → (P → R) → (Q → R) → (P ∨ Q) → R
  p→r+q→r+p∨q=r pr _ (∨-intro₀ p) = pr p
  p→r+q→r+p∨q=r _ qr (∨-intro₁ q) = qr q

  ∨-comm′ : ∀ {P Q} → (P ∨ Q) → (Q ∨ P)
  ∨-comm′ (∨-intro₀ p) = ∨-intro₁ p
  ∨-comm′ (∨-intro₁ q) = ∨-intro₀ q

------------------------------------------------------------------------
-- public aliases

∨-elim : ∀ {P Q n} {R : Set n} → (P → R) → (Q → R) → (P ∨ Q) → R
∨-elim = p→r+q→r+p∨q=r

∨-comm : ∀ {P Q} → (P ∨ Q) ⇔ (Q ∨ P)
∨-comm = ∧-intro ∨-comm′ ∨-comm′
