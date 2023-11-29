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

SGlueᶠ : (φ : Γ → CofProp)
  (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
  (B : Γ ⊢ᶠType ℓ)
  (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
  → Γ ⊢ᶠType ℓ
SGlueᶠ φ A B fe =
  Realignᶠ φ A (Glueᶠ φ A B fe) (includeAIsoᴵ φ (equivFun fe))

opaque
  SGlueᶠStrictness : (φ : Γ → CofProp)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (B : Γ ⊢ᶠType ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
    → A ≡ SGlueᶠ φ A B fe ∘ᶠ fst
  SGlueᶠStrictness φ A B fe =
    isRealignedFib φ _ _ (includeAIsoᴵ φ (equivFun fe))

opaque
  reindexSGlueᶠ : (φ : Γ → CofProp)
    (B : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ B (A ∘ᶠ fst))
    (ρ : Δ → Γ)
    → SGlueᶠ φ B A fe ∘ᶠ ρ ≡ SGlueᶠ (φ ∘ ρ) (B ∘ᶠ ρ ×id) (A ∘ᶠ ρ) (fe ∘ ρ ×id)
  reindexSGlueᶠ φ (_ , β) (_ , α) fe ρ =
    reindexRealignᶠ φ _ _ _ ρ
    ∙
    cong
      (λ α' → Realignᶠ (φ ∘ ρ) _ (_ , α') (includeAIsoᴵ (φ ∘ ρ) _))
      (reindexGlueFibStr φ β α fe ρ)
