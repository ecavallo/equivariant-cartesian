{-

Realigning strict glue.

-}
{-# OPTIONS --rewriting #-}
module glueing.aligned where

open import prelude
open import axioms
open import fibrations
open import equivs
open import realignment

open import glueing.weak
open import glueing.strict

----------------------------------------------------------------------
-- Realigning strict glue
----------------------------------------------------------------------

abstract
  FibSGlue : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Π (Equiv' A (B ∘ fst)))
    → ---------------
    isFib A → isFib B → isFib (SGlue' Φ A B (equivFun fe))
  FibSGlue {Γ = Γ} Φ {A} {B} fe α β =
    realign Φ (SGlue' Φ A B (equivFun fe))
      (subst isFib (SGlueStrictness' Φ (equivFun fe)) α)
      (Misaligned.FibSGlue Φ fe α β)

  FibSGlueStrictness : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Π (Equiv' A (B ∘ fst)))
    (α : isFib A) (β : isFib B)
    → ---------------
    subst isFib (SGlueStrictness' Φ (equivFun fe)) α
    ≡ reindex (SGlue' Φ A B (equivFun fe)) (FibSGlue Φ fe α β) fst
  FibSGlueStrictness Φ {A} {B} fe α β =
    symm
      (isRealigned Φ (SGlue' Φ A B (equivFun fe))
        (subst isFib (SGlueStrictness' Φ (equivFun fe)) α)
        (Misaligned.FibSGlue Φ fe α β))

SGlueFib : ∀ {ℓ ℓ'}
  {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (Aα : Fib ℓ' (res Γ Φ))
  (Bβ : Fib ℓ' Γ)
  (fe : Π (Equiv' (Aα .fst) (Bβ .fst ∘ fst)))
  → Fib ℓ' Γ
SGlueFib {Γ = Γ} Φ (A , α) (B , β) fe = (_ , FibSGlue Φ fe α β)

SGlueFibStrictness : ∀ {ℓ ℓ'}
  {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (Aα : Fib ℓ' (res Γ Φ))
  (Bβ : Fib ℓ' Γ)
  (fe : Π (Equiv' (Aα .fst) (Bβ .fst ∘ fst)))
  → Aα ≡ reindex' (SGlueFib Φ Aα Bβ fe) fst
SGlueFibStrictness Φ (A , α) (B , β) fe =
  Σext (SGlueStrictness' Φ (equivFun fe)) (FibSGlueStrictness Φ fe α β)

abstract
  reindexSGlue :
    ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set ℓ''}
    {B : Γ → Set ℓ''}
    (fe : Π (Equiv' A (B ∘ fst)))
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (SGlue' Φ A B (equivFun fe)) (FibSGlue Φ fe α β) ρ
      ≡ FibSGlue (Φ ∘ ρ) (fe ∘ (ρ ×id)) (reindex A α (ρ ×id)) (reindex B β ρ)
  reindexSGlue Φ {A} {B} fe α β ρ =
    trans
      (cong₂ (realign (Φ ∘ ρ) (SGlue' Φ A B (equivFun fe) ∘ ρ))
        (reindexSubst (ρ ×id)
          (SGlueStrictness' Φ (equivFun fe))
          (SGlueStrictness' (Φ ∘ ρ) (equivFun fe ∘ (ρ ×id))) α)
        (Misaligned.reindexSGlue Φ fe α β ρ))
      (reindexRealign Φ (SGlue' Φ A B (equivFun fe))
        (subst isFib (SGlueStrictness' Φ (equivFun fe)) α)
        (Misaligned.FibSGlue Φ fe α β)
        ρ)
