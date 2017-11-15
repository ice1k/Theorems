module Bools where

open import Agda.Builtin.Bool public

not : Bool → Bool
not true  = false
not false = true

-- T : Bool → Set
-- T true  = ⊤
-- T false = ⊥

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b
