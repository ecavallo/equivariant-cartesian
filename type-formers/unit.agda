{-

Fibrancy of the unit type.

-}
{-# OPTIONS --rewriting #-}
module type-formers.unit where

open import prelude
open import axioms
open import fibration.fibration

UnitIsFib : ∀ {ℓ} {Γ : Set ℓ} → isFib (λ(_ : Γ) → Unit)
UnitIsFib .lift _ _ _ _ .fill _ .out = tt
UnitIsFib .lift _ _ _ _ .fill _ .out≡ u = refl
UnitIsFib .lift _ _ _ _ .cap≡ = refl
UnitIsFib .vary _ _ _ _ _ _ _ = refl
