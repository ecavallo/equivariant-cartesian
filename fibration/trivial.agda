{-

Definition of trivial fibration structure.

-}
module fibration.trivial where

open import prelude
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

TFibStr : {Γ : Type ℓ} (A : Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
TFibStr {Γ = Γ} A = (γ : Γ) (φ : Cof) (a : [ φ ] → A γ) → A γ [ φ ↦ a ]

opaque
  TFibStrToFibStr : {Γ : Type ℓ} {A : Γ → Type ℓ'} → TFibStr A → FibStr A
  TFibStrToFibStr c .lift S r p box =
    fitsPartialToFiller λ s →
    c (p s) (box .cof ∨ S ∋ r ≈ s) (boxToPartial box s)
  TFibStrToFibStr c .vary S T σ r p box s =
    congΣ ((out ∘_) ∘ c (p (⟪ σ ⟫ s))) cofEq $
    substDom [_] cofEq _
    ∙ funExt (λ u → varyBoxToPartial σ box s (subst [_] (sym cofEq) u) u)
    where
    cofEq : (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (box .cof ∨ S ∋ r ≈ s)
    cofEq = cong (box .cof ∨_) (≈Equivariant σ r s)

_⊢ᶠTriv_ : (Γ : Type ℓ) (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Γ ⊢ᶠTriv ℓ' = Σ (Γ → Type ℓ') TFibStr

TFibToFib : Γ ⊢ᶠTriv ℓ → Γ ⊢ᶠType ℓ
TFibToFib A .fst = A .fst
TFibToFib A .snd = TFibStrToFibStr (A .snd)
