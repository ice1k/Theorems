module PosNat where

open import Nats
open import Data.Product
open import Agda.Builtin.Equality

data ℕ⁺ : Set where
  psuc : ℕ → ℕ⁺

_→ℕ : ℕ⁺ → ℕ
psuc  zero   →ℕ = suc  zero
psuc (suc x) →ℕ = suc (psuc x →ℕ)

_⟨_⟩→ℕ⁺ : (a : ℕ) → ∃ (λ x → a ≡ suc x) → ℕ⁺
.(suc x) ⟨ x , refl ⟩→ℕ⁺ = psuc x
