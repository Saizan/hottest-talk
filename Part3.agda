{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude


record Stream (A : Type₀) : Type₀ where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

open Stream


mapS : ∀ {A B} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)


mapS-id : ∀ {A} (xs : Stream A) → mapS (λ x → x) xs ≡ xs
head (mapS-id xs i) = head xs
tail (mapS-id xs i) = mapS-id (tail xs) i
