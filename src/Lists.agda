module Lists where

open import Nats
open import Bools

open import Agda.Builtin.List public
  using (List; []; _∷_)

infixr 5 _++_ _∷ʳ_

[_] : ∀ {a} {A : Set a} → A → List A
[ x ] = x ∷ []

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_∷ʳ_ : ∀ {a} {A : Set a} → List A → A → List A
xs ∷ʳ x = xs ++ [ x ]

null : ∀ {a} {A : Set a} → List A → 𝔹
null []       = true
null (x ∷ xs) = false

reverse : ∀ {a} {A : Set a} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ∷ʳ x

replicate : ∀ {a} {A : Set a} → (n : ℕ) → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x
