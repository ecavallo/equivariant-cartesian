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

--↓ Type of contractibility structures on a type.

Contr : Type ℓ → Type ℓ
Contr A = ((φ , a) : A ⁺) → A [ φ ↦ a ]

--↓ Type of trivial fibration structures on a family.

TFibStr : {Γ : Type ℓ} (A : Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
TFibStr A = ∀ γ → Contr (A γ)

--↓ Type of trivial fibrations in a given context.

_⊢ᶠTriv_ : (Γ : Type ℓ) (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Γ ⊢ᶠTriv ℓ' = Σ (Γ → Type ℓ') TFibStr

--↓ Any trivial fibration structure induces a fibration structure.

opaque
  TFibStrToFibStr : {A : Γ → Type ℓ'} → TFibStr A → FibStr A
  TFibStrToFibStr c .lift S γ r box =
    fitsPartialToFiller λ s →
    c (γ s) (box .cof ∨ S ∋ r ≈ s , boxToPartial box s)
  TFibStrToFibStr c .vary S T σ γ r box s =
    cong (out ∘ c _) $
    Σext cofEq $
    substDom [_] cofEq _
    ∙ funExt (λ u → reshapeBoxToPartial σ box s (subst [_] (sym cofEq) u) u)
    where
    cofEq : (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (box .cof ∨ S ∋ r ≈ s)
    cofEq = cong (box .cof ∨_) (≈Equivariant σ r s)

  reindexTFibStrToFibStr : {A : Γ → Type ℓ} {c : TFibStr A} (ρ : Δ → Γ)
    → TFibStrToFibStr c ∘ᶠˢ ρ ≡ TFibStrToFibStr (c ∘ ρ)
  reindexTFibStrToFibStr ρ = refl

TFibToFib : Γ ⊢ᶠTriv ℓ → Γ ⊢ᶠType ℓ
TFibToFib A .fst = A .fst
TFibToFib A .snd = TFibStrToFibStr (A .snd)

--↓ Reindexing for trivial fibrations.

_∘ᵗᶠ_ : (A : Γ ⊢ᶠTriv ℓ) (ρ : Δ → Γ) → Δ ⊢ᶠTriv ℓ
(A ∘ᵗᶠ ρ) .fst = A .fst ∘ ρ
(A ∘ᵗᶠ ρ) .snd = A .snd ∘ ρ

--↓ Forgetting that a fibration is trivial commutes with reindexing.

opaque
  reindexTFibToFib : {A : Γ ⊢ᶠTriv ℓ} (ρ : Δ → Γ)
    → TFibToFib A ∘ᶠ ρ ≡ TFibToFib (A ∘ᵗᶠ ρ)
  reindexTFibToFib ρ = Σext refl (reindexTFibStrToFibStr ρ)
