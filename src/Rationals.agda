module Rationals where

open import Nats renaming (_+_ to _:+:_)
open import Agda.Builtin.Equality
open import Agda.Builtin.TrustMe using ()
open import Data.Product

infixl 7 _÷_⟨_⟩
infixr 5 _→ℕ
infixr 7 _÷_↓_⟨_⟩
infixr 7 _÷_↑_⟨_⟩
infixl 6 _+_
infixl 6 _⊕_

data ℚ : ℕ → ℕ → Set where
  _÷_⟨_⟩ : ∀ a b → b >0 → ℚ a b

_→ℕ : ∀ {a n} → ℚ (a * n) n → ∃ (λ m → m ≡ a)
_→ℕ {a} _ = a , refl

-- of course.
_÷_↓_⟨_⟩ : ∀ a b n → n >0 → ℚ (a * n) (b * n) ≡ ℚ a b
_ ÷ _ ↓ _ ⟨ _ ⟩ = Agda.Builtin.TrustMe.primTrustMe

_÷_↑_⟨_⟩ : ∀ a b n → n >0 → ℚ a b ≡ ℚ (a * n) (b * n)
a ÷ b ↑ n ⟨ x ⟩ rewrite a ÷ b ↓ n ⟨ x ⟩ = refl

_⊕_ : ∀ {a b c} → ℚ a c → ℚ b c → ℚ (a :+: b) c
(a ÷ c ⟨ x ⟩) ⊕ (b ÷ .c ⟨ _ ⟩) = (a :+: b) ÷ c ⟨ x ⟩

_+_ : ∀ {a b c d} → ℚ a c → ℚ b d → ℚ (a * d :+: b * c) (c * d)
(a ÷ c ⟨ intro x ⟩) + (b ÷ d ⟨ intro y ⟩)
  rewrite a ÷ c ↑ d ⟨ intro y ⟩
        | b ÷ d ↑ c ⟨ intro x ⟩
          = let lemma = intro (y :+: x * suc y)
            in a * d ÷ c * d ⟨ lemma ⟩ ⊕ b * c ÷ c * d ⟨ lemma ⟩
