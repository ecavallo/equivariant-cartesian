{-

Fibrancy of the unit type.

-}
{-# OPTIONS --rewriting #-}
module type-formers.unit where

open import prelude
open import axioms
open import fibration.fibration

UnitIsFib : ∀ {ℓ} {Γ : Set ℓ} → isFib (λ(_ : Γ) → Unit)
UnitIsFib .lift _ _ _ _ _ (unit , _) .comp _ = (unit , λ _ → refl)
UnitIsFib .lift _ _ _ _ _ (unit , _) .cap = refl
UnitIsFib .vary _ _ _ _ _ _ _ (unit , _) _ = refl
