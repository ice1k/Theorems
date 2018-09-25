module Tuples where

open import Data.Product

_² : ∀ {a} (A : Set a) → Set a
A ² = A × A

_³ : ∀ {a} (A : Set a) → Set a
A ³ = A × A ²

_⁴ : ∀ {a} (A : Set a) → Set a
A ⁴ = A × A ³

_⁵ : ∀ {a} (A : Set a) → Set a
A ⁵ = A × A ⁴

_⁶ : ∀ {a} (A : Set a) → Set a
A ⁶ = A × A ⁵

_⁷ : ∀ {a} (A : Set a) → Set a
A ⁷ = A × A ⁶

