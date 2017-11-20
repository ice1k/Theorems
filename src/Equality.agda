module Equality where

open import Agda.Builtin.Equality public

infix 4 _≅_

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
   refl : x ≅ x

≡→≅ : ∀ {ℓ} {a b : Set ℓ} → a ≡ b → a ≅ b
≡→≅ refl = refl
