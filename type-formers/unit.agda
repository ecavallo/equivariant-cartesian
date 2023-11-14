{-

Fibrancy of the unit type.

-}
{-# OPTIONS --rewriting #-}
module type-formers.unit where

open import prelude
open import axioms
open import fibration.fibration

𝟙IsFib : ∀ {ℓ} {Γ : Set ℓ} → isFib (λ(_ : Γ) → 𝟙)
𝟙IsFib .lift _ _ _ _ .fill _ .out = tt
𝟙IsFib .lift _ _ _ _ .fill _ .out≡ u = refl
𝟙IsFib .lift _ _ _ _ .cap≡ = refl
𝟙IsFib .vary _ _ _ _ _ _ _ = refl
