{-

Definition and basic properties of (strict) retracts.

-}
module basic.retract where

open import basic.prelude
open import basic.equality
open import basic.function
open import basic.isomorphism
open import axiom.funext

private variable
  ℓ ℓ' : Level

record Retract (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
 constructor makeRetract
 field
  sec : A → B
  ret : B → A
  inv : ∀ a → ret (sec a) ≡ a

open Retract public

retractExt : {A : Type ℓ} {B : Type ℓ'}
  {retract₀ retract₁ : Retract A B}
  → retract₀ .sec ≡ retract₁ .sec
  → retract₀ .ret ≡ retract₁ .ret
  → retract₀ ≡ retract₁
retractExt refl refl = cong (makeRetract _ _) (funExt' $ uip')

isoToRetract : {A : Type ℓ} {B : Type ℓ'}
  → A ≅ B → Retract A B
isoToRetract iso .sec = iso .to
isoToRetract iso .ret = iso .from
isoToRetract iso .inv = iso .inv₁
