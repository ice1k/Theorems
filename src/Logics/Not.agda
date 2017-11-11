module Logics.Not where

open import Logics.And
open import Logics.Or

open import Data.Empty

open import Relation.Nullary

open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- public aliases

-- can anybody help
-- neg-neg-id : ∀ {ℓ} (a : Set ℓ) → ¬ (¬ a) ≡ a
-- neg-neg-id a = ⊥-elim {!!}
