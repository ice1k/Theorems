module Groups.Symm.S3 where

open import Equality

------------------------------------------------------------------------
-- definitions

bin-op : ∀ {ℓ} (A : Set ℓ) → Set ℓ
bin-op A = A → A → A

------------------------------------------------------------------------
-- internal stuffs

private

  record S₃ {ℓ} (A : Set ℓ) : Set ℓ where
    constructor ⟨_,_,_⟩-⟨_,_,_⟩-⟨_,_,_⟩
    infixl 5 _×_
    field
      x y {e} : A
      _×_ : bin-op A
      assoc : ∀ a b c → a × b × c ≡ a × (b × c)      
      idₗ : ∀ n → n × e ≡ n
      idᵣ : ∀ n → e × n ≡ n
      law-xxx=e : x × x × x ≡ e
      law-yy=e : y × y ≡ e
      law-yx=xxy : y × x ≡ x × x × y

    law-xyx=y : Set ℓ
    law-xyx=y = x × y × x ≡ y

    xyx=y : law-xyx=y
    xyx=y
      rewrite assoc x y x
            | law-yx=xxy
            | sym (assoc x (x × x) y)
            | sym (assoc x x x)
            | law-xxx=e
              = idᵣ y

------------------------------------------------------------------------
-- public aliases

s3-property-1 : ∀ {ℓ} (A : S₃ (Set ℓ)) → S₃.law-xyx=y A
s3-property-1 = S₃.xyx=y
