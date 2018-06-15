module Nats.Add.Invert where

open import Equality
open import Nats
open import Nats.Add.Comm
open import Function

------------------------------------------------------------------------
-- internal stuffs

private

  lemma′ : ∀ a b → (suc a ≡ suc b) → (a ≡ b)
  lemma′ _ _ refl = refl

  lemma : ∀ a b → (suc (a + suc a) ≡ suc (b + suc b)) → (a + a ≡ b + b)
  lemma a b
    rewrite nat-add-comm a $ suc a
          | nat-add-comm b $ suc b
            = lemma′ (a + a) (b + b) ∘ lemma′ (suc $ a + a) (suc $ b + b)

  +-invert : ∀ a b → (a + a ≡ b + b) → a ≡ b
  +-invert zero zero ev = refl
  +-invert zero (suc b) ()
  +-invert (suc a) zero ()
  +-invert (suc a) (suc b) ev
    rewrite +-invert a b $ lemma a b ev = refl

------------------------------------------------------------------------
-- public aliases

nat-add-invert : ∀ a b → (a + a ≡ b + b) → a ≡ b
nat-add-invert = +-invert

nat-add-invert-1 : ∀ a b → (suc a ≡ suc b) → (a ≡ b)
nat-add-invert-1 = lemma′
