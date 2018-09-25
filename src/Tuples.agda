module Tuples where

open import Data.Product

_² : ∀ {a} (A : Set a) → Set a
A ² = A × A

_³ : ∀ {a} (A : Set a) → Set a
A ³ = A ² × A

_⁴ : ∀ {a} (A : Set a) → Set a
A ⁴ = A ³ × A

_⁵ : ∀ {a} (A : Set a) → Set a
A ⁵ = A ⁴ × A

_⁶ : ∀ {a} (A : Set a) → Set a
A ⁶ = A ⁵ × A

_⁷ : ∀ {a} (A : Set a) → Set a
A ⁷ = A ⁶ × A

