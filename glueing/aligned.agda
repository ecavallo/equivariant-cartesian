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

----------------------------------------------------------------------
-- Realigning strict glue
----------------------------------------------------------------------

abstract
  SGlueIsFib : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Π (Equiv' A (B ∘ fst)))
    → ---------------
    isFib A → isFib B → isFib (SGlue' Φ A B (equivFun fe))
  SGlueIsFib {Γ = Γ} Φ {A} {B} fe α β =
    realignIsFib Φ (SGlue' Φ A B (equivFun fe))
      (subst isFib (SGlueStrictness' Φ (equivFun fe)) α)
      (Misaligned.SGlueIsFib Φ fe α β)

  SGlueIsFibStrictness : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Π (Equiv' A (B ∘ fst)))
    (α : isFib A) (β : isFib B)
    → ---------------
    subst isFib (SGlueStrictness' Φ (equivFun fe)) α
    ≡ reindex (SGlue' Φ A B (equivFun fe)) (SGlueIsFib Φ fe α β) fst
  SGlueIsFibStrictness Φ {A} {B} fe α β =
    symm
      (isRealigned Φ (SGlue' Φ A B (equivFun fe))
        (subst isFib (SGlueStrictness' Φ (equivFun fe)) α)
        (Misaligned.SGlueIsFib Φ fe α β))

FibSGlue : ∀ {ℓ ℓ'}
  {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (Aα : Fib ℓ' (Γ ,[ Φ ]))
  (Bβ : Fib ℓ' Γ)
  (fe : Π (Equiv' (Aα .fst) (Bβ .fst ∘ fst)))
  → Fib ℓ' Γ
FibSGlue {Γ = Γ} Φ (A , α) (B , β) fe = (_ , SGlueIsFib Φ fe α β)

FibSGlueStrictness : ∀ {ℓ ℓ'}
  {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (Aα : Fib ℓ' (Γ ,[ Φ ]))
  (Bβ : Fib ℓ' Γ)
  (fe : Π (Equiv' (Aα .fst) (Bβ .fst ∘ fst)))
  → Aα ≡ reindexFib (FibSGlue Φ Aα Bβ fe) fst
FibSGlueStrictness Φ (A , α) (B , β) fe =
  Σext (SGlueStrictness' Φ (equivFun fe)) (SGlueIsFibStrictness Φ fe α β)

abstract
  reindexSGlue :
    ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ''}
    {B : Γ → Set ℓ''}
    (fe : Π (Equiv' A (B ∘ fst)))
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (SGlue' Φ A B (equivFun fe)) (SGlueIsFib Φ fe α β) ρ
      ≡ SGlueIsFib (Φ ∘ ρ) (fe ∘ (ρ ×id)) (reindex A α (ρ ×id)) (reindex B β ρ)
  reindexSGlue Φ {A} {B} fe α β ρ =
    trans
      (cong₂ (realignIsFib (Φ ∘ ρ) (SGlue' Φ A B (equivFun fe) ∘ ρ))
        (reindexSubst (ρ ×id)
          (SGlueStrictness' Φ (equivFun fe))
          (SGlueStrictness' (Φ ∘ ρ) (equivFun fe ∘ (ρ ×id))) α)
        (Misaligned.reindexSGlue Φ fe α β ρ))
      (reindexRealignIsFib Φ (SGlue' Φ A B (equivFun fe))
        (subst isFib (SGlueStrictness' Φ (equivFun fe)) α)
        (Misaligned.SGlueIsFib Φ fe α β)
        ρ)
