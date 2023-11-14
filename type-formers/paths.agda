{-

Fibrancy of Path types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.paths where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.extension

record _~_ {ℓ} {A : Set ℓ}(a a' : A) : Set ℓ where
  constructor path
  field
    at : 𝕀 → A
    at0 : at 0 ≡ a
    at1 : at 1 ≡ a'

open _~_ public

eqToPath : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ~ y
eqToPath {x = x} p = path (λ _ → x) refl p

refl~ : ∀{ℓ} {A : Set ℓ} (a : A) → a ~ a
refl~ a = eqToPath refl

PathExt : ∀{ℓ} {A : Set ℓ} {a a' : A} {p q : a ~ a'}
  → (∀ i → p .at i ≡ q .at i) → p ≡ q
PathExt {A = A} {a} {a'} t =
  cong
    {A = Σ (𝕀 → A) λ p → Σ (p 0 ≡ a) (λ _ → p 1 ≡ a')}
    (λ {(l , l₀ , l₁) → path l l₀ l₁})
    (Σext (funext t) (Σext uipImp uipImp))

Path' : ∀{ℓ ℓ'}{Γ : Set ℓ}(A : Γ → Set ℓ') → Σ x ∈ Γ , A x × A x → Set ℓ'
Path' A (x , (a , a')) = a ~ a'

opaque
  private
    ctxMap : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A : Γ → Set ℓ')
      → Σ x ∈ Γ , A x × A x → Σ x ∈ Γ , Partial 𝕚 ∂ (A ∘ fst) x
    ctxMap A (γ , a₀ , a₁) = γ , λ i → OI-rec i (λ _ → a₀) (λ _ → a₁)

    retract : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A : Γ → Set ℓ')
      → Retract' (Path' A) (Extension' 𝕚 ∂ (A ∘ fst) ∘ ctxMap A)
    retract A γ .sec p i .out = p .at i
    retract A γ .sec p i .out≡ = OI-elim i (λ {refl → symm (p .at0)}) (λ {refl → symm (p .at1)})
    retract A γ .ret ex .at i = ex i .out
    retract A γ .ret ex .at0 = symm (ex 0 .out≡ ∣ inl refl ∣)
    retract A γ .ret ex .at1 = symm (ex 1 .out≡ ∣ inr refl ∣)
    retract A γ .inv = funext λ p → PathExt λ i → refl

  PathIsFib :
    ∀{ℓ ℓ'} {Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    (α : isFib A)
    → -----------
    isFib (Path' A)
  PathIsFib {ℓ' = ℓ'} {Γ} {A} α =
    retractIsFib (retract A) (reindex (ExtensionIsFib 𝕚 ∂ (reindex α fst)) (ctxMap A))

  ----------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------
  reindexPath :
    ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (PathIsFib α) (ρ ×id) ≡ PathIsFib (reindex α ρ)
  reindexPath {A = A} α ρ =
    reindexRetract
      (retract A)
      (reindex (ExtensionIsFib 𝕚 ∂ (reindex α fst)) (ctxMap A))
      (ρ ×id)
    ∙
    cong₂
      retractIsFib
      (funext λ _ → retractExt (funext λ _ → funext λ _ → restrictExt refl) refl)
      (reindexComp (ExtensionIsFib 𝕚 ∂ (reindex α fst)) (ρ ×id) (ctxMap A)
        ∙ cong (λ fib → reindex fib (ctxMap (A ∘ ρ))) (reindexExtension (reindex α fst) ρ))
