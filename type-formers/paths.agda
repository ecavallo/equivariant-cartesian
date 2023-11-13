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
    at : Int → A
    atO : at O ≡ a
    atI : at I ≡ a'

open _~_ public

eqToPath : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ~ y
eqToPath {x = x} p = path (λ _ → x) refl p

refl~ : ∀{ℓ} {A : Set ℓ} (a : A) → a ~ a
refl~ a = eqToPath refl

PathExt : ∀{ℓ} {A : Set ℓ} {a a' : A} {p q : a ~ a'}
  → (∀ i → p .at i ≡ q .at i) → p ≡ q
PathExt {A = A} {a} {a'} t =
  cong
    {A = Σ (Int → A) λ p → Σ (p O ≡ a) (λ _ → p I ≡ a')}
    (λ {(l , l₀ , l₁) → path l l₀ l₁})
    (Σext (funext t) (Σext uipImp uipImp))

Path' : ∀{ℓ ℓ'}{Γ : Set ℓ}(A : Γ → Set ℓ') → Σ x ∈ Γ , A x × A x → Set ℓ'
Path' A (x , (a , a')) = a ~ a'

abstract
  private
    ctxMap : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A : Γ → Set ℓ')
      → Σ x ∈ Γ , A x × A x → Σ x ∈ Γ , Partial int ∂ (A ∘ fst) x
    ctxMap A (γ , a₀ , a₁) = γ , λ i → OI-rec i (λ _ → a₀) (λ _ → a₁)

    retract : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A : Γ → Set ℓ')
      → Retract' (Path' A) (Extension' int ∂ (A ∘ fst) ∘ ctxMap A)
    retract A γ .sec p i .fst = p .at i
    retract A γ .sec p i .snd = OI-elim i (λ {refl → symm (p .atO)}) (λ {refl → symm (p .atI)})
    retract A γ .ret ex .at i = ex i .fst
    retract A γ .ret ex .atO = symm (ex O .snd ∣ inl refl ∣)
    retract A γ .ret ex .atI = symm (ex I .snd ∣ inr refl ∣)
    retract A γ .inv = funext λ p → PathExt λ i → refl

  PathIsFib :
    ∀{ℓ ℓ'} {Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    (α : isFib A)
    → -----------
    isFib (Path' A)
  PathIsFib {ℓ' = ℓ'} {Γ} {A} α =
    retractIsFib
      (Path' A)
      (Extension' int ∂ (A ∘ fst) ∘ ctxMap A)
      (retract A)
      (reindex (Extension' int ∂ (A ∘ fst)) (ExtensionIsFib int ∂ (reindex A α fst)) (ctxMap A))

  ----------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------
  reindexPath :
    ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ → Set ℓ'')
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Path' A) (PathIsFib α) (ρ ×id) ≡ PathIsFib (reindex A α ρ)
  reindexPath A α ρ =
    reindexRetract
      (retract A)
      (reindex (Extension' int ∂ (A ∘ fst)) (ExtensionIsFib int ∂ (reindex A α fst)) (ctxMap A))
      (ρ ×id)
    ∙
    cong₂
      (retractIsFib (Path' (A ∘ ρ)) (Extension' int ∂ (A ∘ ρ ∘ fst) ∘ ctxMap (A ∘ ρ)))
      (funext λ _ → retractExt (funext λ _ → funext λ _ → Σext refl (funext λ _ → uipImp)) refl)
      (reindexComp (ExtensionIsFib int ∂ (reindex A α fst)) (ρ ×id) (ctxMap A)
        ∙ cong (λ fib → reindex (Extension' int ∂ (A ∘ ρ ∘ fst)) fib (ctxMap (A ∘ ρ)))
              (reindexExtension int ∂ (A ∘ fst) (reindex A α fst) ρ))
