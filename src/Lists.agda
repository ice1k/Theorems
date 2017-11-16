module Lists where

open import Nats
open import Bools

open import Agda.Builtin.List public
  using (List; []; _∷_)

infixr 5 _++_ _∷ʳ_

[_] : ∀ {ℓ} {A : Set ℓ} → A → List A
[ x ] = x ∷ []

_++_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_∷ʳ_ : ∀ {ℓ} {A : Set ℓ} → List A → A → List A
xs ∷ʳ x = xs ++ [ x ]

null : ∀ {ℓ} {A : Set ℓ} → List A → 𝔹
null []       = true
null (x ∷ xs) = false

reverse : ∀ {ℓ} {A : Set ℓ} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ∷ʳ x

replicate : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x
