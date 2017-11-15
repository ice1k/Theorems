module Isos.NatLike where

open import Isos.Isomorphism

open import Nats
open import Data.Product

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

------------------------------------------------------------------------
-- internal stuffs

private

  module WithList where

  open import Lists

  list→ℕ : List ⊤ → ℕ
  list→ℕ  []      = zero
  list→ℕ (tt ∷ a) = suc (list→ℕ a)

  ℕ→list : ℕ → List ⊤
  ℕ→list  zero   = []
  ℕ→list (suc a) = tt ∷ ℕ→list a

  module WithVec where

  open import Vecs

  vec→ℕ′ : ∀ {n} → Vec ⊤ n → ℕ
  vec→ℕ′ {n}  []      = n
  vec→ℕ′ {n} (tt ∷ a) = n

  vec→ℕ : ∀ {n} → Vec ⊤ n → ∃ (λ m → n ≡ m)
  vec→ℕ  []      = zero , refl
  vec→ℕ (tt ∷ a) with vec→ℕ a
  ...               | m , refl = suc m , refl

  ℕ→vec : ∀ {n} → ∃ (λ m → n ≡ m) → Vec ⊤ n
  ℕ→vec  (zero   , refl) = []
  ℕ→vec ((suc a) , refl) = tt ∷ ℕ→vec (a , refl)

iso-nat-list : ℕ ⇔ List ⊤
iso-nat-list = ∧-intro ℕ→list list→ℕ

iso-nat-vec : ∀ {n} → ∃ (λ m → n ≡ m) ⇔ Vec ⊤ n
iso-nat-vec = ∧-intro ℕ→vec vec→ℕ
