{-

Fibrancy of the unit type.

-}
module type-former.unit where

open import prelude
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ : Level
  Γ : Type ℓ

𝟙FibStr : FibStr (λ (_ : Γ) → 𝟙)
𝟙FibStr .lift _ _ _ _ .fill _ .out = tt
𝟙FibStr .lift _ _ _ _ .fill _ .out≡ u = refl
𝟙FibStr .lift _ _ _ _ .cap≡ = refl
𝟙FibStr .vary _ _ _ _ _ _ _ = refl

𝟙ᶠ : Γ ⊢ᶠType lzero
𝟙ᶠ .fst _ = 𝟙
𝟙ᶠ .snd = 𝟙FibStr
