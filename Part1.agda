{-# OPTIONS --cubical #-}

-- https://github.com/agda/cubical
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool
open import Cubical.Data.List


private
  variable
    A B : Type _


_ : I
_ = i0

_ : I
_ = i1


refl' : (x : A) → x ≡ x
refl' x = \ i → x



funExt' : {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
funExt' p i x = p x i


















subst' : (C : A → Type) → ∀ {x y : A} → x ≡ y → C x → C y
subst' C p c = transp (\ i → C (p i)) i0 c

{-

   T : I → Type   r : I   r = i1 |- T constant    t : T i0
   --------------------------------------------------------
   transp T r t : T i1


   r = 1 |- T i0 = T i1

   transp T i1 t = t

-}

subst'-refl : (C : A → Type) → ∀ {x} → (c : C x) → subst C refl c ≡ c
subst'-refl C {x} c i = transp (\ i → C x) i c

subst'-over : (C : A → Type) → ∀ {x y} → (c : C x) (p : x ≡ y)
              → PathP (\ i → C (p i)) c (subst C p c)
subst'-over C {x} c p j = transp (\ i → C (p (i ∧ j))) (~ j) c

-- ~ j = i1   <=> j = i0




-- The ua constant
ua' : ∀ {A B : Type} → A ≃ B → A ≡ B
ua' {A = A} {B = B} e i = Glue B {i ∨ ~ i} (λ { (i = i0) → (A , e)
                                              ; (i = i1) → (B , idEquiv B) })

{-
  X : Type    r = i1 |- e : Σ[ T ∈ Type ] T ≃ X
  ----------------------------------------------
          Glue X e : Type
-}


notEquiv' : Bool ≃ Bool
notEquiv' = not , notIsEquiv


_ : subst' List (ua notEquiv') (true ∷ []) ≡ false ∷ []
_ = refl
