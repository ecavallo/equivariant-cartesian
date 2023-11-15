{-

Fibrancy of the empty type.

-}
{-# OPTIONS --rewriting #-}
module type-formers.empty where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ : Level

𝟘IsFib : {Γ : Type ℓ} → isFib (λ(_ : Γ) → 𝟘)
𝟘IsFib .lift _ _ _ box = 𝟘-rec (box .cap .out)
𝟘IsFib .vary _ _ _ _ _ box = 𝟘-rec (box .cap .out)
