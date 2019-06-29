{-

Realigning strict glue.

-}
{-# OPTIONS --rewriting #-}
module glueing.aligned where

open import glueing.core
open import glueing.strict

open import prelude
open import interval
open import cofprop
open import fibrations
open import equivs
open import realignment

----------------------------------------------------------------------
-- Realigning strict glue
----------------------------------------------------------------------

abstract
  FibSGlue :
    ∀{a}{Γ : Set a}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set}
    {B : Γ → Set}
    (fe : Π (Equiv' A (B ∘ fst)))
    → ---------------
    isFib A → isFib B → isFib (SGlue' Φ A B (equivFun fe))
  FibSGlue {a} {Γ} Φ {A} {B} fe α β =
    realign Φ (SGlue' Φ A B (equivFun fe))
      (subst isFib (SGlueStrictness' Φ (equivFun fe)) α)
      (Misaligned.FibSGlue Φ fe α β)

  FibSGlueStrictness :
    {ℓ : Level}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set}
    {B : Γ → Set}
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

SGlueFib :
  ∀{a}{Γ : Set a}
  (Φ : Γ → CofProp)
  (Aα : Fib (res Γ Φ))
  (Bβ : Fib Γ)
  (fe : Π (Equiv' (Aα .fst) (Bβ .fst ∘ fst)))
  → Fib Γ
SGlueFib {a} {Γ} Φ (A , α) (B , β) fe = (_ , FibSGlue Φ fe α β)

SGlueFibStrictness :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (Aα : Fib (res Γ Φ))
  (Bβ : Fib Γ)
  (fe : Π (Equiv' (Aα .fst) (Bβ .fst ∘ fst)))
  → Aα ≡ reindex' (SGlueFib Φ Aα Bβ fe) fst
SGlueFibStrictness Φ (A , α) (B , β) fe =
  Σext (SGlueStrictness' Φ (equivFun fe)) (FibSGlueStrictness Φ fe α β)

abstract
  reindexSGlue :
    ∀ {ℓ} {Δ Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set}
    {B : Γ → Set}
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
