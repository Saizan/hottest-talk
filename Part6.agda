{-# OPTIONS --cubical --guarded #-}

open import Types
open import Later
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.ListedFiniteSet renaming (LFSet to Pfin)

_ : ∀ {l} {A : Type l} → (▹ A → A) → A
_ = fix

-- ▹ A 0 = Unit
-- ▹ A (suc n) = A n

next' : {A : Type} → A → ▹ A
next' a = \ α → a

_ : ∀ {A : Type} → (f : ▹ A → A) → fix f ≡ f (next' (fix f))
_ = \ f → fix-eq f

-- fail : {A : Type} → ▹ (▹ A) → ▹ A
-- fail x = {!\ α → (x α) α!}


data Delay (A : Type) : Type where
  now  : A           → Delay A
  step : ▹ (Delay A) → Delay A

bind : ∀ {A B : Type} → (A → Delay B) → Delay A → Delay B
bind f = fix \ bind' → \ { (now x) → f x ; (step x) → step \ α → bind' α (x α) }

_>>=_ : ∀ {A B : Type} → Delay A → (A → Delay B) → Delay B
d >>= f = bind f d

D : Type
D = fix \ X → Delay (▸ \ α → X α → X α)

inD : Delay (▸ \ α → D → D) → D
inD = transport (sym (fix-eq _))

outD : D → Delay (▸ \ α → D → D)
outD = transport (fix-eq _)

δ : Delay D → D
δ d = inD (bind outD d)

_·_ : D → D → D
d · d' = δ (outD d >>= \ f → step \ α → now (f α d'))

abs : (D → D) → D
abs f = inD (now \ α → f)




{-
Bisimulation as path type for guarded recursive types
Rasmus Ejlers Møgelberg, Niccolò Veltri

https://arxiv.org/abs/1810.13261
-}

Proc : Type → Type
Proc A = fix \ X → Pfin (A × (▸ \ α → X α))



{-
Formalizing 𝜋-calculus in guarded cubical Agda
Niccolò Veltri, Andrea Vezzosi

https://dl.acm.org/doi/10.1145/3372885.3373814
-}
