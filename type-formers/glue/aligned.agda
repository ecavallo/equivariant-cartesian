{-

Realigned (ie "strict") glue types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.glue.aligned where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.realignment
open import type-formers.equivs
open import type-formers.glue.weak

private variable
  ℓ : Level
  Γ Δ : Type ℓ

SGlueᶠ : (φ : Γ → Cof)
  (B : Γ ⊢ᶠType ℓ)
  (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
  (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
  → Γ ⊢ᶠType ℓ
SGlueᶠ φ B A fe =
  ≅Realignᶠ φ (Glueᶠ φ B A fe) A (includeAIsoᴵ φ (equivFun fe))

opaque
  SGlueᶠStrictness : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
    → A ≡ SGlueᶠ φ B A fe ∘ᶠ fst
  SGlueᶠStrictness φ B A fe =
    ≅RealignᶠMatch φ _ _ (includeAIsoᴵ φ (equivFun fe))

opaque
  reindexSGlueᶠ : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
    (ρ : Δ → Γ)
    → SGlueᶠ φ B A fe ∘ᶠ ρ ≡ SGlueᶠ (φ ∘ ρ) (B ∘ᶠ ρ) (A ∘ᶠ ρ ×id) (fe ∘ ρ ×id)
  reindexSGlueᶠ φ (_ , β) (_ , α) fe ρ =
    reindexRealignᶠ _ _ _ _ _
    ∙
    cong
      (λ β' → ≅Realignᶠ _ (_ , β') _ (includeAIsoᴵ (φ ∘ ρ) _))
      (reindexGlueFibStr _ _ _ _ _)
