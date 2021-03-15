{-# OPTIONS --cubical --guarded #-}
module Later where

open import Agda.Builtin.Equality renaming (_≡_ to _≣_)
open import Agda.Builtin.Sigma

open import Cubical.Foundations.Prelude

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

-- The behaviour of fix is encoded with rewrite rules, following the
-- definitional equalities of TCTT.
postulate
  dfix : ∀ {l} {A : Set l} → (f : ▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} → (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

abstract
  fix : ∀ {l} {A : Set l} → (f : ▹ A → A) → A
  fix f = f (pfix f i0)

  fix-eq : ∀ {l} {A : Set l} → (f : ▹ A → A) → fix f ≡ f (next (fix f))
  fix-eq f = cong f (pfix f)
