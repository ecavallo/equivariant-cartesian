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

SGlueᶠ : (Φ : Γ → CofProp)
  (A : Γ ▷[ Φ ] ⊢ᶠType ℓ)
  (B : Γ ⊢ᶠType ℓ)
  (fe : Γ ▷[ Φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
  → Γ ⊢ᶠType ℓ
SGlueᶠ Φ A B fe =
  Realignᶠ Φ A (Glueᶠ Φ A B fe) (includeAIsoᴵ Φ (equivFun fe))

opaque
  SGlueᶠStrictness : (Φ : Γ → CofProp)
    (A : Γ ▷[ Φ ] ⊢ᶠType ℓ)
    (B : Γ ⊢ᶠType ℓ)
    (fe : Γ ▷[ Φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
    → A ≡ SGlueᶠ Φ A B fe ∘ᶠ fst
  SGlueᶠStrictness Φ A B fe =
    isRealignedFib Φ _ _ (includeAIsoᴵ Φ (equivFun fe))

opaque
  reindexSGlueᶠ : (Φ : Γ → CofProp)
    (B : Γ ▷[ Φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (fe : Γ ▷[ Φ ] ⊢ᶠ Equivᶠ B (A ∘ᶠ fst))
    (ρ : Δ → Γ)
    → SGlueᶠ Φ B A fe ∘ᶠ ρ ≡ SGlueᶠ (Φ ∘ ρ) (B ∘ᶠ ρ ×id) (A ∘ᶠ ρ) (fe ∘ ρ ×id)
  reindexSGlueᶠ Φ (_ , β) (_ , α) fe ρ =
    reindexRealignᶠ Φ _ _ _ ρ
    ∙
    cong
      (λ α' → Realignᶠ (Φ ∘ ρ) _ (_ , α') (includeAIsoᴵ (Φ ∘ ρ) _))
      (reindexGlueFibStr Φ β α fe ρ)
