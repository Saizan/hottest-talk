{-




                                  Cubical Agda and its extensions


                              Andrea Vezzosi - IT University Copenhagen


                                    HoTTEST Seminar 11/03/2021












-}
open import Types

-- MLTT Identity type.

data _≡_ {A : Type} (x : A) : A → Type where
  refl : x ≡ x

-- refl is the only canonical form.
-- no room for principles like function extensinality or univalence.


{-
Cubical Type Theory: a constructive interpretation of the univalence axiom

Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg
https://arxiv.org/abs/1611.02108


-- equalities as maps from an abstract interval (pre-)type.
-}
