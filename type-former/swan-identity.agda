{-

Fibration structure on Swan identity types, assuming a dominance and cofibration extensionality.

-}
module type-former.swan-identity where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration
open import fibration.trivial
open import type-former.path
open import type-former.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

--↓ Definition of dominance with a limited form of cofibration extensionality

record Dominance : Type where
  field
    _∧_ : (φ : Cof) → ([ φ ] → Cof) → Cof
    ∧-pair : ∀ {φ ψ} → (u : [ φ ]) → [ ψ u ] → [ φ ∧ ψ ]
    ∧-fst : ∀ {φ ψ} → [ φ ∧ ψ ] → [ φ ]
    ∧-snd : ∀ {φ ψ} → (uv : [ φ ∧ ψ ]) → [ ψ (∧-fst uv) ]
    ∧-ext : ∀ {φ ψ} → (u : [ φ ]) → φ ∧ ψ ≡ ψ u

module SwanIdentity (Dom : Dominance) where

  open Dominance Dom

  Constancy : {A : Type ℓ} {a₀ a₁ : A} (p : a₀ ~ a₁) → Type ℓ
  Constancy p = Σ φ ∈ Cof , ((i : 𝕀) → [ φ ] → p .at i ≡ p .at 0)

  ConstancyExt : {A : Type ℓ} {a₀ a₁ : A} (p : a₀ ~ a₁) {c₀ c₁ : Constancy p}
    → c₀ .fst ≡ c₁ .fst
    → c₀ ≡ c₁
  ConstancyExt _ eq = Σext eq (funExt' $ funExt' uip')

  Id : {A : Type ℓ} (a₀ a₁ : A) → Type ℓ
  Id a₀ a₁ = Σ (a₀ ~ a₁) Constancy

  IdExt : {A : Type ℓ} {a₀ a₁ : A} {q₀ q₁ : Id a₀ a₁}
    → (∀ i → q₀ .fst .at i ≡ q₁ .fst .at i)
    → q₀ .snd .fst ≡ q₁ .snd .fst
    → q₀ ≡ q₁
  IdExt {q₀ = q₀} {q₁} eq₀ eq₁ = lemma (PathExt eq₀)
    where
    lemma : q₀ .fst ≡ q₁ .fst → q₀ ≡ q₁
    lemma refl = Σext refl (ConstancyExt (q₀ .fst) eq₁)

  Constancyˣ : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ˣ A} (p : Γ ⊢ˣ Pathˣ A a₀ a₁) → (Γ → Type ℓ)
  Constancyˣ p γ = Constancy (p γ)

  Idˣ : (A : Γ → Type ℓ) (a₀ a₁ : Γ ⊢ˣ A) → (Γ → Type ℓ)
  Idˣ A a₀ a₁ γ = Id (a₀ γ) (a₁ γ)

  ConstancyIsTFib : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ˣ A} (p : Γ ⊢ˣ Pathˣ A a₀ a₁)
    → TFibStr (Constancyˣ p)
  ConstancyIsTFib p γ φ a .out .fst = φ ∧ λ u → a u .fst
  ConstancyIsTFib p γ φ a .out .snd i uv = a (∧-fst uv) .snd i (∧-snd uv)
  ConstancyIsTFib p γ φ a .out≡ u = ConstancyExt (p γ) (sym (∧-ext u))

  Idᶠ : (A : Γ ⊢ᶠType ℓ) (a₀ a₁ : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
  Idᶠ A a₀ a₁ = Σᶠ (Pathᶠ A a₀ a₁) (TFibToFib (_ , ConstancyIsTFib 𝒒))

  opaque
    unfolding TFibStrToFibStr
    reindexIdᶠ : {A : Γ ⊢ᶠType ℓ} {a₀ a₁ : Γ ⊢ᶠ A}
      (ρ : Δ → Γ) → Idᶠ A a₀ a₁ ∘ᶠ ρ ≡ Idᶠ (A ∘ᶠ ρ) (a₀ ∘ ρ) (a₁ ∘ ρ)
    reindexIdᶠ ρ =
      reindexΣᶠ ρ ∙
      congΣ Σᶠ
        (reindexPathᶠ ρ)
        (substCongAssoc (λ A → _ ▷ˣ A ⊢ᶠType _) ∣_∣ (reindexPathᶠ ρ) _
          ∙ cong (subst (λ A → _ ▷ˣ A ⊢ᶠType _) ⦅–⦆ _) (uip _ refl))

  idreflᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠ Idᶠ A a a
  idreflᶠ A a γ .fst = refl~ (a γ)
  idreflᶠ A a γ .snd .fst = 𝕚 ∋ 0 ≈ 0
  idreflᶠ A a γ .snd .snd _ _ = refl

  -- TODO J
