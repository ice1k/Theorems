module Logics.And where

------------------------------------------------------------------------
-- definitions

data _∧_ (P Q : Set) : Set where
  ∧-intro : P → Q → P ∧ Q

_⇔_ : (P Q : Set) → Set
p ⇔ q = (p → q) ∧ (q → p)

------------------------------------------------------------------------
-- internal stuffs

private

  ∧-comm′ : ∀ {P Q} → (P ∧ Q) → (Q ∧ P)
  ∧-comm′ (∧-intro p q) = (∧-intro q p)

  ∧-assoc₀ : ∀ {P Q R} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
  ∧-assoc₀ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

  ∧-assoc₁ : ∀ {P Q R} → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
  ∧-assoc₁ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

------------------------------------------------------------------------
-- public aliases

∧-comm : ∀ {P Q} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm = ∧-intro ∧-comm′ ∧-comm′

∧-assoc : ∀ {P Q R} → (P ∧ (Q ∧ R)) ⇔ ((P ∧ Q) ∧ R)
∧-assoc = ∧-intro ∧-assoc₁ ∧-assoc₀

