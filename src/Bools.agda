module Bools where

open import Agda.Builtin.Bool public
  renaming (Bool to 𝔹)

not : 𝔹 → 𝔹
not true  = false
not false = true

-- T : 𝔹 → Set
-- T true  = ⊤
-- T false = ⊥

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if true  then t else _ = t
if false then _ else f = f

_∧_ : 𝔹 → 𝔹 → 𝔹
true  ∧ b = b
false ∧ _ = false

_∨_ : 𝔹 → 𝔹 → 𝔹
true  ∨ _ = true
false ∨ b = b

_xor_ : 𝔹 → 𝔹 → 𝔹
true  xor b = not b
false xor b = b
