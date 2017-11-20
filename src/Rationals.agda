module Rationals where

open import Nats renaming (_+_ to _:+:_)
open import Equality
open import Agda.Builtin.TrustMe using ()
open import Data.Product

infixl 7 _÷_⟨_⟩
infixr 5 _→ℕ
infixr 7 _÷_↓_⟨_,_⟩
infixr 7 _÷_↑_⟨_,_⟩
infixl 6 _+_

data ℚ : Set where
  _÷_⟨_⟩ : (a b : ℕ) → b >0 → ℚ

_→ℕ : {a : ℕ} → ℚ → ∃ (λ m → m ≡ a)
_→ℕ {a} _ = a , refl

-- of course.
_÷_↓_⟨_,_⟩ : ∀ a b n → (r₀ : n >0) → (r₁ : b >0) →
           let x = n >0 in
           (a * n ÷ b * n ⟨ r₁ *>0 r₀ ⟩) ≡ a ÷ b ⟨ r₁ ⟩
_ ÷ _ ↓ _ ⟨ _ , _ ⟩ = Agda.Builtin.TrustMe.primTrustMe

div-mul-comm : ∀ a c d → (x : c >0) → (y : d >0) → a ÷ c * d ⟨ x *>0 y ⟩ ≡ a ÷ d * c ⟨ y *>0 x ⟩
div-mul-comm _ _ _ _ _ = Agda.Builtin.TrustMe.primTrustMe

_÷_↑_⟨_,_⟩ : ∀ a b n → (r₀ : n >0) → (r₁ : b >0) →
           a ÷ b ⟨ r₁ ⟩ ≡ (a * n ÷ b * n ⟨ r₁ *>0 r₀ ⟩)
a ÷ b ↑ n ⟨ x , y ⟩ rewrite a ÷ b ↓ n ⟨ x , y ⟩ = refl

_+_ : ℚ → ℚ → ℚ
a ÷ c ⟨ x ⟩ + b ÷ d ⟨ y ⟩ = (a * d :+: b * c) ÷ c * d ⟨ x *>0 y ⟩
