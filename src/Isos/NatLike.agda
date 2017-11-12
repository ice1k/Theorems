module Isos.NatLike where

open import Isos.Isomorphism

open import Data.Nat
open import Data.Unit

------------------------------------------------------------------------
-- internal stuffs

private

  module WithList where

  open import Data.List

  list→ℕ : List ⊤ → ℕ
  list→ℕ  []      = zero
  list→ℕ (tt ∷ a) = suc (list→ℕ a)

  ℕ→list : ℕ → List ⊤
  ℕ→list  zero   = []
  ℕ→list (suc a) = tt ∷ ℕ→list a

  module WithVec where

  open import Data.Vec

  vec→ℕ : ∀ {n} → Vec ⊤ n → ℕ
  vec→ℕ  []      = zero
  vec→ℕ (tt ∷ a) = suc (vec→ℕ a)

  ℕ→vec : (n : ℕ) → Vec ⊤ n
  ℕ→vec  zero   = []
  ℕ→vec (suc a) = tt ∷ ℕ→vec a

iso-nat-list : ℕ ⇔ List ⊤
iso-nat-list = ∧-intro ℕ→list list→ℕ
