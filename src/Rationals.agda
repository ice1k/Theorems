module Rationals where

open import Nats renaming (_+_ to _:+:_; _*_ to _:*:_)
open import Equality
open import Agda.Builtin.TrustMe using ()
open import Data.Product

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
_ ÷ _ ↓ _ = Agda.Builtin.TrustMe.primTrustMe

_÷_↑_ : ∀ a b n → a ÷ b ≡ (a :*: n ÷ (b :*: n))
a ÷ b ↑ n rewrite a ÷ b ↓ n = refl

_+_ : ℚ → ℚ → ℚ
a ÷ c + b ÷ d = (a :*: d :+: b :*: c) ÷ (c :*: d)

_*_ : ℚ → ℚ → ℚ
(a ÷ c) * (b ÷ d) = a :*: b ÷ (c :*: d)

_/_ : ℚ → ℚ → ℚ
(a ÷ c) / (b ÷ d) = a :*: d ÷ (c :*: b)
