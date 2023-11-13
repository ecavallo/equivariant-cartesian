{-

Fibrancy of the empty type.

-}
{-# OPTIONS --rewriting #-}
module type-formers.empty where

open import prelude
open import axioms
open import fibration.fibration

∅IsFib : ∀ {ℓ} {Γ : Set ℓ} → isFib (λ(_ : Γ) → ∅)
∅IsFib .lift _ _ _ box = ∅-rec (box .cap .fst)
∅IsFib .vary _ _ _ _ _ box = ∅-rec (box .cap .fst)
