module Rationals where

open import Nats renaming (_+_ to _:+:_; _*_ to _:*:_)
open import Equality
open import Data.Product
open import Agda.Builtin.TrustMe

infixl 7 _÷_
infixr 5 _→ℕ
infixr 7 _÷_↓_
infixr 7 _÷_↑_
infixl 6 _+_

data ℚ : Set where
  _÷_ : (a b : ℕ) → ℚ

_→ℕ : {a : ℕ} → ℚ → ∃ (λ m → m ≡ a)
_→ℕ {a} _ = a , refl

-- of course.
_÷_↓_ : ∀ a b n → (a :*: n ÷ (b :*: n)) ≡ a ÷ b
_ ÷ _ ↓ _ = primTrustMe

_÷_↑_ : ∀ a b n → a ÷ b ≡ (a :*: n ÷ (b :*: n))
a ÷ b ↑ n = sym (a ÷ b ↓ n)

_+_ : ℚ → ℚ → ℚ
a ÷ c + b ÷ d = (a :*: d :+: b :*: c) ÷ (c :*: d)

_*_ : ℚ → ℚ → ℚ
(a ÷ c) * (b ÷ d) = a :*: b ÷ (c :*: d)

_/_ : ℚ → ℚ → ℚ
(a ÷ c) / (b ÷ d) = a :*: d ÷ (c :*: b)
