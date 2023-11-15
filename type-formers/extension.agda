{-

Fibrancy of extension types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.extension where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ ℓ' ℓ'' : Level

-- TODO do something better with this
Partial : (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
  {Γ : Set ℓ}
  (A : Γ × ⟨ Z ⟩ → Set ℓ')
  → Γ → Set ℓ'
Partial Z Φ A γ = ∀ z → [ Φ z ] → A (γ , z)

Extensionᴵ : (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
  {Γ : Set ℓ}
  (A : Γ × ⟨ Z ⟩ → Set ℓ')
  → Σ Γ (Partial Z Φ A) → Set ℓ'
Extensionᴵ Z Φ A (γ , a) = (z : ⟨ Z ⟩) → A (γ , z) [ Φ z ↦ a z ]

module ExtensionLift {Z Φ S r}
  {A : ⟨ S ⟩ × ⟨ Z ⟩ → Set ℓ} (α : isFib A)
  {a : ⟨ S ⟩ ⊢ Partial Z Φ A}
  (box : OpenBox S r (Extensionᴵ Z Φ A ∘ (id ,, a)))
  where

  module _ (z : ⟨ Z ⟩) where

    boxA : OpenBox S r (λ s → A (s , z))
    boxA .cof = box .cof ∨ Φ z
    boxA .tube =
      ∨-rec (box .cof) (Φ z)
        (λ u s → box .tube u s z .out)
        (λ v s → a s z v)
        (λ u v → funext λ s → sym (box .tube u s z .out≡ v))
    boxA .cap .out = box .cap .out z .out
    boxA .cap .out≡ =
      ∨-elimEq (box .cof) (Φ z)
        (λ u → cong (λ q → q z .out) (box .cap .out≡ u))
        (λ v → box .cap .out z .out≡ v)

    fillA = α .lift S r (_, z) boxA

  filler : Filler box
  filler .fill s .out z .out = fillA z .fill s .out
  filler .fill s .out z .out≡ v = fillA z .fill s .out≡ (∨r v)
  filler .fill s .out≡ u = funext λ z → restrictExt (fillA z .fill s .out≡ (∨l u))
  filler .cap≡ = funext λ z → restrictExt (fillA z .cap≡)

module ExtensionVary {Z Φ S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ × ⟨ Z ⟩ → Set ℓ} (α : isFib A)
  {a : ⟨ T ⟩ ⊢ Partial Z Φ A}
  (box : OpenBox T (⟪ σ ⟫ r) (Extensionᴵ Z Φ A ∘ (id ,, a)))
  where

  module T = ExtensionLift α box
  module S = ExtensionLift (reindex α (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    funext λ z →
    restrictExt
      (α .vary S T σ r (_, z) (T.boxA z) s
        ∙ cong (λ b → α .lift S r ((_, z) ∘ ⟪ σ ⟫) b .fill s .out)
            (boxExt refl
              (diagonalElim (box .cof ∨ Φ z)
                (∨-elimEq (box .cof) (Φ z) (λ _ → refl) (λ _ → refl)))
              refl))

opaque
  ExtensionIsFib : (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
    {Γ : Set ℓ}
    {A : Γ × ⟨ Z ⟩ → Set ℓ'}
    (α : isFib A)
    → isFib (Extensionᴵ Z Φ A)
  ExtensionIsFib Z Φ α .lift S r p = ExtensionLift.filler (reindex α ((fst ∘ p) ×id))
  ExtensionIsFib Z Φ α .vary S T σ r p = ExtensionVary.eq σ (reindex α ((fst ∘ p) ×id))

  ----------------------------------------------------------------------
  -- Forming extension types is stable under reindexing
  ----------------------------------------------------------------------
  reindexExtension : {Z : Shape} {Φ : ⟨ Z ⟩ → CofProp}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ × ⟨ Z ⟩ → Set ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (ExtensionIsFib Z Φ α) (ρ ×id) ≡ ExtensionIsFib Z Φ (reindex α (ρ ×id))
  reindexExtension α ρ = isFibExt λ _ _ _ _ _ → refl
