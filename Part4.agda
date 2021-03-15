{-# OPTIONS --two-level --without-K #-}

open import Types

data _≣_ {A : Type} (x : A) : A → SSet where
  reflSEq : x ≣ x


hasK : {A : Type} {C : ∀ x → x ≣ x → Type} {x : A} → C x reflSEq → (p : x ≣ x) → C x p
hasK c reflSEq = c


data _≡_ {A : Type} (x : A) : A → Type where
  reflEq : x ≡ x


strict-to-fibrant : ∀ {A : Type} {x y : A} → x ≣ y → x ≡ y
strict-to-fibrant reflSEq = reflEq

{-
fibrant-to-strict : ∀ {A : Type} {x y : A} → x ≡ y → x ≣ y
fibrant-to-strict reflEq = reflSEq
-}


{-

Extending Homotopy Type Theory with Strict Equality
-- Thorsten Altenkirch, Paolo Capriotti, Nicolai Kraus

https://arxiv.org/abs/1604.03799

-}
