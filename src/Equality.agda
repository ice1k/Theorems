module Equality where

open import Agda.Builtin.Equality public
open import Relation.Nullary

infix 4 _≅_ _≢_
infixr 2 _≡⟨_⟩_
infix  3 _QED

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
   refl : x ≅ x

≡→≅ : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → a ≅ b
≡→≅ refl = refl

sym : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

sym′ : ∀ {ℓ} {A B : Set ℓ} {a : A} {b : B} → a ≅ b → b ≅ a
sym′ refl = refl

subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
         {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl p = p

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
x ≢ y = ¬ x ≡ y

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A}
       → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

_QED : ∀ {A : Set} (x : A) → x ≡ x
x QED = refl
