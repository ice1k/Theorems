module Ints where

open import Nats public
  using (ℕ; zero; _∸_)
  renaming (suc to nsuc; _+_ to _:+:_; _*_ to _:*:_)
open import Agda.Builtin.Int public
  renaming (Int to ℤ; negsuc to -[1+_]; pos to +_)

infix  8 -_
-- infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊖_

∣_∣ : ℤ → ℕ
∣ + n      ∣ = n
∣ -[1+ n ] ∣ = nsuc n

-_ : ℤ → ℤ
- (+ nsuc n) = -[1+ n ]
- (+ zero)   = + zero
- -[1+ n ]   = + nsuc n

_⊖_ : ℕ → ℕ → ℤ
m      ⊖ zero   = + m
zero   ⊖ nsuc n = -[1+ n ]
nsuc m ⊖ nsuc n = m ⊖ n

_+_ : ℤ → ℤ → ℤ
-[1+ m ] + -[1+ n ] = -[1+ nsuc (m :+: n) ]
-[1+ m ] + +    n   = n ⊖ nsuc m
+    m   + -[1+ n ] = m ⊖ nsuc n
+    m   + +    n   = + (m :+: n)

_-_ : ℤ → ℤ → ℤ
i - j = i + - j

suc : ℤ → ℤ
suc i = + 1 + i
