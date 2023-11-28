{-

Fibrancy of Path types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.paths where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.extension
open import type-formers.sigma

private variable
  ℓ : Level
  Γ Δ : Type ℓ

record _~_ {A : Type ℓ} (a a' : A) : Type ℓ where
  constructor path
  field
    at : 𝕀 → A
    at0 : at 0 ≡ a
    at1 : at 1 ≡ a'

open _~_ public

eqToPath : {A : Type ℓ} {x y : A} → x ≡ y → x ~ y
eqToPath {x = x} p = path (λ _ → x) refl p

refl~ : {A : Type ℓ} (a : A) → a ~ a
refl~ a = eqToPath refl

PathExt : {A : Type ℓ} {a a' : A} {p q : a ~ a'}
  → (∀ i → p .at i ≡ q .at i) → p ≡ q
PathExt t =
  cong (uncurry (uncurry ∘ path)) (Σext (funext t) (Σext uipImp uipImp))

Pathᴵ : (A : Γ → Type ℓ) (a₀ a₁ : Γ ⊢ A) → Γ → Type ℓ
Pathᴵ A a₀ a₁ γ = a₀ γ ~ a₁ γ

opaque
  private
    partialEl : {A : Γ → Type ℓ} (a₀ a₁ : Γ ⊢ A)
      → (Γ × 𝕀) ,[ ∂ ∘ snd ] ⊢ A ∘ fst ∘ wk[ ∂ ∘ snd ]
    partialEl a₀ a₁ =
      uncurry λ (γ , i) → OI-rec i (λ _ → a₀ γ) (λ _ → a₁ γ)

    retract : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ A}
      → Γ ⊢ Retractᴵ (Pathᴵ A a₀ a₁) (Extensionᴵ 𝕚 (A ∘ fst) ∂ (partialEl a₀ a₁))
    retract γ .sec p i .out = p .at i
    retract γ .sec p i .out≡ =
      OI-elim i (λ {refl → sym (p .at0)}) (λ {refl → sym (p .at1)})
    retract γ .ret ex .at i = ex i .out
    retract γ .ret ex .at0 = sym (ex 0 .out≡ (∨l refl))
    retract γ .ret ex .at1 = sym (ex 1 .out≡ (∨r refl))
    retract γ .inv = funext λ p → PathExt λ i → refl

  PathFibStr : {A : Γ → Type ℓ} (α : FibStr A) (a₀ a₁ : Γ ⊢ A)
    → FibStr (Pathᴵ A a₀ a₁)
  PathFibStr α a₀ a₁ =
    retractFibStr retract (ExtensionFibStr 𝕚 (α ∘ᶠˢ fst) ∂ _)

  ----------------------------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------------------------

  reindexPathFibStr : {A : Γ → Type ℓ} (α : FibStr A)
    {a₀ a₁ : Γ ⊢ A}
    (ρ : Δ → Γ)
    → PathFibStr α a₀ a₁ ∘ᶠˢ ρ ≡ PathFibStr (α ∘ᶠˢ ρ) (a₀ ∘ ρ) (a₁ ∘ ρ)
  reindexPathFibStr α ρ =
    reindexRetractFibStr retract (ExtensionFibStr 𝕚 (α ∘ᶠˢ fst) ∂ _) ρ
    ∙
    cong₂
      retractFibStr
      (funext λ _ → retractExt (funext λ _ → funext λ _ → restrictExt refl) refl)
      (reindexExtensionFibStr (α ∘ᶠˢ fst) ρ)

Pathᶠ : (A : Γ ⊢ᶠType ℓ) (a₀ a₁ : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
Pathᶠ A a₀ a₁ .fst = Pathᴵ (A .fst) a₀ a₁
Pathᶠ A a₀ a₁ .snd = PathFibStr (A .snd) a₀ a₁

reindexPathᶠ : (A : Γ ⊢ᶠType ℓ) {a₀ a₁ : Γ ⊢ A .fst}
  (ρ : Δ → Γ) → Pathᶠ A a₀ a₁ ∘ᶠ ρ ≡ Pathᶠ (A ∘ᶠ ρ) (a₀ ∘ ρ) (a₁ ∘ ρ)
reindexPathᶠ A ρ = Σext refl (reindexPathFibStr (A .snd) ρ)

-- TODO J rule
