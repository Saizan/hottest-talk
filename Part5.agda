{-# OPTIONS --cubical #-}

open import Types
open import Cubical.Foundations.Prelude
open import Part4 hiding (_≡_)

_ : SSet
_ = I

record Path2 {A : Type} (x y : A) : SSet where
  constructor con
  field
    path : I → A
    path0 : path i0 ≣ x
    path1 : path i1 ≣ y

module _ {A : Type} {x y : A} where
  fwdP : x ≡ y → Path2 x y
  fwdP p = con (\ i → p i) reflSEq reflSEq

  bwdP : Path2 x y → x ≡ y
  bwdP (con f reflSEq reflSEq) = \ i → f i
