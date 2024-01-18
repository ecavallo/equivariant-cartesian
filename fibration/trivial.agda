{-

Definition of trivial fibration structure.

-}
module fibration.trivial where

open import basic
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

TFibStr : {Γ : Type ℓ} (A : Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
TFibStr {Γ = Γ} A = (γ : Γ) (φ : Cof) (a : [ φ ] → A γ) → A γ [ φ ↦ a ]

opaque
  TFibStrToFibStr : {A : Γ → Type ℓ'} → TFibStr A → FibStr A
  TFibStrToFibStr c .lift S γ r box =
    fitsPartialToFiller λ s →
    c (γ s) (box .cof ∨ S ∋ r ≈ s) (boxToPartial box s)
  TFibStrToFibStr c .vary S T σ γ r box s =
    congΣ ((out ∘_) ∘ c (γ (⟪ σ ⟫ s))) cofEq $
    substDom [_] cofEq _
    ∙ funExt (λ u → varyBoxToPartial σ box s (subst [_] (sym cofEq) u) u)
    where
    cofEq : (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (box .cof ∨ S ∋ r ≈ s)
    cofEq = cong (box .cof ∨_) (≈Equivariant σ r s)

  reindexTFibStrToFibStr : {A : Γ → Type ℓ} {c : TFibStr A} (ρ : Δ → Γ)
    → TFibStrToFibStr c ∘ᶠˢ ρ ≡ TFibStrToFibStr (c ∘ ρ)
  reindexTFibStrToFibStr ρ = refl


_⊢ᶠTriv_ : (Γ : Type ℓ) (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Γ ⊢ᶠTriv ℓ' = Σ (Γ → Type ℓ') TFibStr

_∘ᵗ_ : (A : Γ ⊢ᶠTriv ℓ) (ρ : Δ → Γ) → Δ ⊢ᶠTriv ℓ
(A ∘ᵗ ρ) .fst = A .fst ∘ ρ
(A ∘ᵗ ρ) .snd = A .snd ∘ ρ

TFibToFib : Γ ⊢ᶠTriv ℓ → Γ ⊢ᶠType ℓ
TFibToFib A .fst = A .fst
TFibToFib A .snd = TFibStrToFibStr (A .snd)

opaque
  reindexTFibToFib : {A : Γ ⊢ᶠTriv ℓ} (ρ : Δ → Γ)
    → TFibToFib A ∘ᶠ ρ ≡ TFibToFib (A ∘ᵗ ρ)
  reindexTFibToFib ρ = Σext refl (reindexTFibStrToFibStr ρ)
