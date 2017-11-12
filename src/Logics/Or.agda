module Logics.Or where

open import Logics.And

------------------------------------------------------------------------
-- definitions

infixl 4 _∨_

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

  ∨-assoc₀ : ∀ {P Q R} → ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R))
  ∨-assoc₀ (∨-intro₀ (∨-intro₀ x)) = ∨-intro₀ x
  ∨-assoc₀ (∨-intro₀ (∨-intro₁ x)) = ∨-intro₁ (∨-intro₀ x)
  ∨-assoc₀ (∨-intro₁ x) = ∨-intro₁ (∨-intro₁ x)

  ∨-assoc₁ : ∀ {P Q R} → (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R)
  ∨-assoc₁ (∨-intro₀ x) = ∨-intro₀ (∨-intro₀ x)
  ∨-assoc₁ (∨-intro₁ (∨-intro₀ x)) = ∨-intro₀ (∨-intro₁ x)
  ∨-assoc₁ (∨-intro₁ (∨-intro₁ x)) = ∨-intro₁ x

  ∨-elim : ∀ {P Q n} {R : Set n} → (P → R) → (Q → R) → (P ∨ Q) → R
  ∨-elim = p→r+q→r+p∨q=r

  ∨-comm : ∀ {P Q} → (P ∨ Q) ⇔ (Q ∨ P)
  ∨-comm = ∧-intro ∨-comm′ ∨-comm′

  ∨-assoc : ∀ {P Q R} → (P ∨ (Q ∨ R)) ⇔ ((P ∨ Q) ∨ R)
  ∨-assoc = ∧-intro ∨-assoc₁ ∨-assoc₀

------------------------------------------------------------------------
-- public aliases

or-elim : ∀ {P Q n} {R : Set n} → (P → R) → (Q → R) → (P ∨ Q) → R
or-elim = ∨-elim

or-comm : ∀ {P Q} → (P ∨ Q) ⇔ (Q ∨ P)
or-comm = ∨-comm

or-assoc : ∀ {P Q R} → (P ∨ (Q ∨ R)) ⇔ ((P ∨ Q) ∨ R)
or-assoc = ∨-assoc
