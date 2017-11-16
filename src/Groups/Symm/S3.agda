module Groups.Symm.S3 where

open import Agda.Builtin.Equality
open import Data.Maybe

------------------------------------------------------------------------
-- definitions

bin-op : ∀ {ℓ} (A : Set ℓ) → Set ℓ
bin-op A = A → A → A

------------------------------------------------------------------------
-- internal stuffs

private

  record S3 {ℓ} (A : Set ℓ) : Set ℓ where
    constructor ⟨_,_,_⟩-⟨_,_,_⟩-⟨_,_,_⟩
    infixl 5 _×_
    field
      x y {e} : A
      _×_ : bin-op A
      assocₗ : ∀ a b c → a × b × c ≡ a × (b × c)      
      idₗ : ∀ n → n × e ≡ n
      idᵣ : ∀ n → e × n ≡ n
      law-xxx=e : x × x × x ≡ e
      law-yy=e : y × y ≡ e
      law-yx=xxy : y × x ≡ x × x × y

    law-xyx=y : Set ℓ
    law-xyx=y = x × y × x ≡ y

    assocᵣ : ∀ a b c → a × (b × c) ≡ a × b × c
    assocᵣ a b c rewrite assocₗ a b c = refl

    s3-xyx=y : law-xyx=y
    s3-xyx=y
      rewrite assocₗ x y x
            | law-yx=xxy
            | assocᵣ x (x × x) y
            | assocᵣ x x x
            | law-xxx=e
              = idᵣ y

------------------------------------------------------------------------
-- public aliases

s3-property-1 : ∀ {ℓ} (A : S3 (Set ℓ)) → S3.law-xyx=y A
s3-property-1 = S3.s3-xyx=y
