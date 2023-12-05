{-

Fibrancy of the empty type.

-}
module type-formers.empty where

open import prelude
open import axioms
open import fibration.fibration

private variable
  ℓ : Level
  Γ : Type ℓ

𝟘FibStr : FibStr (λ (_ : Γ) → 𝟘)
𝟘FibStr .lift _ _ _ box = 𝟘-rec (box .cap .out)
𝟘FibStr .vary _ _ _ _ _ box = 𝟘-rec (box .cap .out)

𝟘ᶠ : Γ ⊢ᶠType lzero
𝟘ᶠ .fst _ = 𝟘
𝟘ᶠ .snd = 𝟘FibStr
