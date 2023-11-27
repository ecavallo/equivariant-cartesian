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

private variable ℓ ℓ' ℓ'' : Level

SGlueᶠ : {Γ : Type ℓ}
  (Φ : Γ → CofProp)
  (A : Fib ℓ' (Γ ,[ Φ ]))
  (B : Fib ℓ' Γ)
  (fe : Γ ,[ Φ ] ⊢ Equivᴵ (A .fst) (B .fst ∘ fst))
  → Fib ℓ' Γ
SGlueᶠ Φ A B fe =
  Realignᶠ Φ A (Glueᶠ Φ A B fe) (includeAIsoᴵ Φ (equivFun fe))

opaque
  SGlueᶠStrictness : {Γ : Type ℓ}
    (Φ : Γ → CofProp)
    (A : Fib ℓ' (Γ ,[ Φ ]))
    (B : Fib ℓ' Γ)
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ (A .fst) (B .fst ∘ fst))
    → A ≡ SGlueᶠ Φ A B fe ∘ᶠ fst
  SGlueᶠStrictness Φ A B fe =
    isRealignedFib Φ _ _ (includeAIsoᴵ Φ (equivFun fe))

opaque
  reindexSGlueᶠ : {Δ : Type ℓ} {Γ : Type ℓ'}
    (Φ : Γ → CofProp)
    (B : Fib ℓ'' (Γ ,[ Φ ]))
    (A : Fib ℓ'' Γ)
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ (B .fst) (A .fst ∘ fst))
    (ρ : Δ → Γ)
    → SGlueᶠ Φ B A fe ∘ᶠ ρ ≡ SGlueᶠ (Φ ∘ ρ) (B ∘ᶠ ρ ×id) (A ∘ᶠ ρ) (fe ∘ ρ ×id)
  reindexSGlueᶠ Φ (_ , β) (_ , α) fe ρ =
    reindexRealignᶠ Φ _ _ _ ρ
    ∙
    cong
      (λ α' → Realignᶠ (Φ ∘ ρ) _ (_ , α') (includeAIsoᴵ (Φ ∘ ρ) _))
      (reindexGlueFibStr Φ β α fe ρ)
