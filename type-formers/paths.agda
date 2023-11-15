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

private variable ℓ ℓ' ℓ'' : Level

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

Pathᴵ : {Γ : Type ℓ} (A : Γ → Type ℓ') → Σ x ∈ Γ , A x × A x → Type ℓ'
Pathᴵ A (x , (a , a')) = a ~ a'

opaque
  private
    ctxMap : {Γ : Type ℓ} (A : Γ → Type ℓ')
      → Σ Γ (A ×ᴵ A) → Σ Γ (Partial 𝕚 ∂ (A ∘ fst))
    ctxMap A (γ , a₀ , a₁) = γ , λ i → OI-rec i (λ _ → a₀) (λ _ → a₁)

    retract : ∀ {ℓ ℓ'} {Γ : Type ℓ} (A : Γ → Type ℓ')
      → Σ Γ (A ×ᴵ A) ⊢ Retractᴵ (Pathᴵ A) (Extensionᴵ 𝕚 ∂ (A ∘ fst) ∘ ctxMap A)
    retract A γ .sec p i .out = p .at i
    retract A γ .sec p i .out≡ = OI-elim i (λ {refl → sym (p .at0)}) (λ {refl → sym (p .at1)})
    retract A γ .ret ex .at i = ex i .out
    retract A γ .ret ex .at0 = sym (ex 0 .out≡ (∨l refl))
    retract A γ .ret ex .at1 = sym (ex 1 .out≡ (∨r refl))
    retract A γ .inv = funext λ p → PathExt λ i → refl

  PathIsFib :{Γ : Type ℓ}
    {A : Γ → Type ℓ'}
    (α : isFib A)
    → -----------
    isFib (Pathᴵ A)
  PathIsFib α =
    retractIsFib (retract _) (reindex (ExtensionIsFib 𝕚 ∂ (reindex α fst)) (ctxMap _))

  ----------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------
  reindexPath : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A : Γ → Type ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (PathIsFib α) (ρ ×id) ≡ PathIsFib (reindex α ρ)
  reindexPath α ρ =
    reindexRetract
      (retract _)
      (reindex (ExtensionIsFib 𝕚 ∂ (reindex α fst)) (ctxMap _))
      (ρ ×id)
    ∙
    cong₂
      retractIsFib
      (funext λ _ → retractExt (funext λ _ → funext λ _ → restrictExt refl) refl)
      (reindexComp (ExtensionIsFib 𝕚 ∂ (reindex α fst)) (ρ ×id) (ctxMap _)
        ∙ cong (λ fib → reindex fib (ctxMap _)) (reindexExtension (reindex α fst) ρ))
