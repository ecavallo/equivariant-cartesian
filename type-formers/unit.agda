{-

Fibrancy of the unit type.

-}
{-# OPTIONS --rewriting #-}
module type-formers.unit where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ : Level

𝟙FibStr : {Γ : Type ℓ} → FibStr (λ (_ : Γ) → 𝟙)
𝟙FibStr .lift _ _ _ _ .fill _ .out = tt
𝟙FibStr .lift _ _ _ _ .fill _ .out≡ u = refl
𝟙FibStr .lift _ _ _ _ .cap≡ = refl
𝟙FibStr .vary _ _ _ _ _ _ _ = refl
