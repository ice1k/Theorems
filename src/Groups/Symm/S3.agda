module Groups.Symm.S3 where

open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- internal stuffs

private

  s3-xyx=y : ∀ {ℓ} {S3 : Set ℓ} (x y e : S3) (_×_ : S3 → S3 → S3) →
       (∀ a b c → (a × b) × c ≡ a × (b × c)) →
       (∀ a b c → a × (b × c) ≡ (a × b) × c) →
       (∀ x → e × x ≡ x) →
       ((x × x) × x ≡ e) →
       (y × y ≡ e) →
       (y × x ≡ (x × x) × y) →
       ((x × y) × x ≡ y)
  s3-xyx=y x y e _×_ assoc assoc-flip id xxx=1 yy=1 yx=xxy
    rewrite assoc x y x
          | yx=xxy
          | assoc-flip x (x × x) y
          | assoc-flip x x x
          | xxx=1
            = id y

------------------------------------------------------------------------
-- public aliases

s3-property-1 : ∀ {ℓ} {S3 : Set ℓ} (x y e : S3) (_×_ : S3 → S3 → S3) →
    (∀ a b c → (a × b) × c ≡ a × (b × c)) →
    (∀ a b c → a × (b × c) ≡ (a × b) × c) →
    (∀ x → e × x ≡ x) →
    ((x × x) × x ≡ e) → (y × y ≡ e) → (y × x ≡ (x × x) × y) →
    ((x × y) × x ≡ y)
s3-property-1 = s3-xyx=y
