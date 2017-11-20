module Rationals.Add.Comm where

open import Equality
open import Nats using (_*_; intro; zero; ℕ; _>0; _*>0_)
                 renaming (suc to s; _+_ to _:+:_)
open import Rationals
open import Rationals.Properties
open import Nats.Add.Comm
open import Nats.Multiply.Distrib
open import Nats.Multiply.Comm

------------------------------------------------------------------------
-- internal stuffs

private

  a/c+b/c=a*b/c : ∀ a b c → (r : c >0) →
                  let q₀ = a ÷ c ⟨ r ⟩ in
                  let q₁ = b ÷ c ⟨ r ⟩ in
                  (q₀ + q₁ ≡ (a :+: b) ÷ c ⟨ r ⟩)
  a/c+b/c=a*b/c a b c i
    rewrite (a :+: b) ÷ c ↑ c ⟨ i , i ⟩
          | nat-multiply-distrib-flip a b c
            = refl

  >0-comm : ∀ a b → (a * b >0) ≡ (b * a >0)
  >0-comm a b rewrite nat-multiply-comm a b = refl

  a+b=b+a : ∀ x y → (x + y) ≡ (y + x)
  a+b=b+a (a ÷ c ⟨ x ⟩) (b ÷ d ⟨ y ⟩)
    rewrite a ÷ c ↑ d ⟨ y , x ⟩
          | b ÷ d ↑ c ⟨ x , y ⟩
          | a/c+b/c=a*b/c (a * d) (b * c) (d * c) (y *>0 x)
          | nat-add-comm (a * d) (b * c)
          | div-mul-comm (b * c :+: a * d) c d x y
            = refl
