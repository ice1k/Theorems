module Vecs where

open import Nats

infixr 5 _∷_ _++_ _∷ʳ_
infix 4 _∈_ _⊛_

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

data _∈_ {a} {A : Set a} : A → {n : ℕ} → Vec A n → Set a where
  here  : ∀ {n} {x}   {xs : Vec A n} → x ∈ x ∷ xs
  there : ∀ {n} {x y} {xs : Vec A n} (x∈xs : x ∈ xs) → x ∈ y ∷ xs

head : ∀ {a n} {A : Set a} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : ∀ {a n} {A : Set a} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

[_] : ∀ {a} {A : Set a} → A → Vec A 1
[ x ] = x ∷ []

_++_ : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_⊛_ : ∀ {a b n} {A : Set a} {B : Set b} →
      Vec (A → B) n → Vec A n → Vec B n
[]       ⊛ _        = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

replicate : ∀ {a n} {A : Set a} → A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

_∷ʳ_ : ∀ {a n} {A : Set a} → Vec A n → A → Vec A (suc n)
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

reverse : ∀ {n m} {A : Set n} → Vec A m → Vec A m
reverse [] = []
reverse (x ∷ xs) = reverse xs ∷ʳ x
