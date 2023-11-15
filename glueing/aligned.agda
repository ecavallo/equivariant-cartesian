{-

Realigning strict glue.

-}
{-# OPTIONS --rewriting #-}
module glueing.aligned where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.realignment
open import type-formers.equivs

open import glueing.weak
open import glueing.strict

private variable ℓ ℓ' ℓ'' : Level

----------------------------------------------------------------------
-- Realigning strict glue
----------------------------------------------------------------------

opaque
  SGlueIsFib : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Π (Equivᴵ A (B ∘ fst)))
    → ---------------
    isFib A → isFib B → isFib (SGlueᴵ Φ A B (equivFun fe))
  SGlueIsFib Φ {A} {B} fe α β =
    realignIsFib Φ (SGlueᴵ Φ A B (equivFun fe))
      (subst isFib (SGlueStrictnessᴵ Φ (equivFun fe)) α)
      (Misaligned.SGlueIsFib Φ fe α β)

  SGlueIsFibStrictness : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Π (Equivᴵ A (B ∘ fst)))
    (α : isFib A) (β : isFib B)
    → ---------------
    subst isFib (SGlueStrictnessᴵ Φ (equivFun fe)) α
    ≡ reindex (SGlueIsFib Φ fe α β) fst
  SGlueIsFibStrictness Φ {A} {B} fe α β =
    sym
      (isRealigned Φ
        (subst isFib (SGlueStrictnessᴵ Φ (equivFun fe)) α)
        (Misaligned.SGlueIsFib Φ fe α β))

FibSGlue : {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (Aα : Fib ℓ' (Γ ,[ Φ ]))
  (Bβ : Fib ℓ' Γ)
  (fe : Π (Equivᴵ (Aα .fst) (Bβ .fst ∘ fst)))
  → Fib ℓ' Γ
FibSGlue Φ (A , α) (B , β) fe = (_ , SGlueIsFib Φ fe α β)

opaque
  FibSGlueStrictness : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    (Aα : Fib ℓ' (Γ ,[ Φ ]))
    (Bβ : Fib ℓ' Γ)
    (fe : Π (Equivᴵ (Aα .fst) (Bβ .fst ∘ fst)))
    → Aα ≡ reindexFib (FibSGlue Φ Aα Bβ fe) fst
  FibSGlueStrictness Φ (A , α) (B , β) fe =
    Σext (SGlueStrictnessᴵ Φ (equivFun fe)) (SGlueIsFibStrictness Φ fe α β)

opaque
  unfolding SGlueIsFib
  reindexSGlue : {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ''}
    {B : Γ → Set ℓ''}
    (fe : Π (Equivᴵ A (B ∘ fst)))
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (SGlueIsFib Φ fe α β) ρ
      ≡ SGlueIsFib (Φ ∘ ρ) (fe ∘ (ρ ×id)) (reindex α (ρ ×id)) (reindex β ρ)
  reindexSGlue Φ {A} {B} fe α β ρ =
    reindexRealignIsFib Φ
      (subst isFib (SGlueStrictnessᴵ Φ (equivFun fe)) α)
      (Misaligned.SGlueIsFib Φ fe α β)
      ρ
    ∙
    cong₂ (realignIsFib (Φ ∘ ρ) (SGlueᴵ Φ A B (equivFun fe) ∘ ρ))
        (reindexSubst (ρ ×id)
          (SGlueStrictnessᴵ Φ (equivFun fe))
          (SGlueStrictnessᴵ (Φ ∘ ρ) (equivFun fe ∘ (ρ ×id))) α)
        (Misaligned.reindexSGlue Φ fe α β ρ)
