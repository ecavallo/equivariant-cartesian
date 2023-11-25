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

FibSGlue : {Γ : Type ℓ}
  (Φ : Γ → CofProp)
  (Aα : Fib ℓ' (Γ ,[ Φ ]))
  (Bβ : Fib ℓ' Γ)
  (fe : Γ ,[ Φ ] ⊢ Equivᴵ (Aα .fst) (Bβ .fst ∘ fst))
  → Fib ℓ' Γ
FibSGlue Φ Aα Bβ fe =
  FibRealign Φ Aα (FibGlue Φ Aα Bβ fe) (includeAIsoᴵ Φ (equivFun fe))

opaque
  FibSGlueStrictness : {Γ : Type ℓ}
    (Φ : Γ → CofProp)
    (Aα : Fib ℓ' (Γ ,[ Φ ]))
    (Bβ : Fib ℓ' Γ)
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ (Aα .fst) (Bβ .fst ∘ fst))
    → Aα ≡ reindexFib (FibSGlue Φ Aα Bβ fe) fst
  FibSGlueStrictness Φ Aα Bβ fe =
    isRealignedFib Φ _ _ (includeAIsoᴵ Φ (equivFun fe))

opaque
  reindexFibSGlue : {Δ : Type ℓ} {Γ : Type ℓ'}
    (Φ : Γ → CofProp)
    (Bβ : Fib ℓ'' (Γ ,[ Φ ]))
    (Aα : Fib ℓ'' Γ)
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ (Bβ .fst) (Aα .fst ∘ fst))
    (ρ : Δ → Γ)
    → reindexFib (FibSGlue Φ Bβ Aα fe) ρ
      ≡ FibSGlue (Φ ∘ ρ)(reindexFib Bβ (ρ ×id)) (reindexFib Aα ρ) (fe ∘ ρ ×id)
  reindexFibSGlue Φ (_ , β) (_ , α) fe ρ =
    reindexFibRealign Φ _ _ _ ρ
    ∙
    cong
      (λ α' → FibRealign (Φ ∘ ρ) _ (_ , α') (includeAIsoᴵ (Φ ∘ ρ) _))
      (reindexGlue Φ fe β α ρ)
