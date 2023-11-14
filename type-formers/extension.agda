{-

Fibrancy of extension types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.extension where

open import prelude
open import axioms
open import fibration.fibration

Partial : ∀ {ℓ ℓ'} (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
  {Γ : Set ℓ}
  → (A : Γ × ⟨ Z ⟩ → Set ℓ')
  → Γ → Set ℓ'
Partial Z Φ A γ = ∀ z → [ Φ z ] → A (γ , z)

Extension' : ∀ {ℓ ℓ'} (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
  {Γ : Set ℓ}
  (A : Γ × ⟨ Z ⟩ → Set ℓ')
  → Σ Γ (Partial Z Φ A) → Set ℓ'
Extension' Z Φ A (γ , a) = (z : ⟨ Z ⟩) → A (γ , z) [ Φ z ↦ a z ]

module ExtensionIsFibId {ℓ}
  {Z : Shape} {Φ : ⟨ Z ⟩ → CofProp}
  {S : Shape}
  {A : ⟨ S ⟩ × ⟨ Z ⟩ → Set ℓ}
  (α : isFib A)
  {a : ∀ s z → [ Φ z ] → A (s , z)}
  {r : ⟨ S ⟩} (box : OpenBox S r (λ s → (Extension' Z Φ A (s , a s))))
  where

  module _ (z : ⟨ Z ⟩) where

    boxA : OpenBox S r (λ s → A (s , z))
    boxA .cof = box .cof ∨ Φ z
    boxA .tube =
      ∨-rec (box .cof) (Φ z)
        (λ u s → box .tube u s z .out)
        (λ v s → a s z v)
        (λ u v → funext λ s → symm (box .tube u s z .out≡ v))
    boxA .cap .out = box .cap .out z .out
    boxA .cap .out≡ =
      ∨-elimEq (box .cof) (Φ z)
        (λ u → cong (λ q → q z .out) (box .cap .out≡ u))
        (λ v → box .cap .out z .out≡ v)

    fillA = α .lift S r (_, z) boxA

opaque
  ExtensionIsFib :
    ∀ {ℓ ℓ'} (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
    {Γ : Set ℓ}
    {A : Γ × ⟨ Z ⟩ → Set ℓ'}
    (α : isFib A)
    → isFib (Extension' Z Φ A)
  ExtensionIsFib Z Φ α .lift S r p box = filler
    where
    open ExtensionIsFibId (reindex α ((fst ∘ p) ×id)) box

    filler : Filler box
    filler .fill s .out z .out = fillA z .fill s .out
    filler .fill s .out z .out≡ v = fillA z .fill s .out≡ ∣ inr v ∣
    filler .fill s .out≡ u = funext λ z → restrictExt (fillA z .fill s .out≡ ∣ inl u ∣)
    filler .cap≡ = funext λ z → restrictExt (fillA z .cap≡)

  ExtensionIsFib Z Φ α .vary S T σ r p box s =
    funext λ z →
    restrictExt
      (α .vary S T σ r (((fst ∘ p) ×id) ∘ (_, z)) (T.boxA z) s
        ∙ cong (λ b → α .lift S r ((fst ∘ p ∘ ⟪ σ ⟫) ×id ∘ (_, z)) b .fill s .out)
            (boxExt refl
              (diagonalElim (box .cof ∨ Φ z)
                (∨-elimEq (box .cof) (Φ z) (λ _ → refl) (λ _ → refl)))
              refl))
    where
    module T = ExtensionIsFibId (reindex α ((fst ∘ p) ×id)) box
    module S = ExtensionIsFibId (reindex α ((fst ∘ p ∘ ⟪ σ ⟫) ×id)) (reshapeBox σ box)

  ----------------------------------------------------------------------
  -- Forming extension types is stable under reindexing
  ----------------------------------------------------------------------
  reindexExtension :
    ∀ {ℓ ℓ' ℓ''} {Z : Shape} {Φ : ⟨ Z ⟩ → CofProp}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ × ⟨ Z ⟩ → Set ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (ExtensionIsFib Z Φ α) (ρ ×id) ≡ ExtensionIsFib Z Φ (reindex α (ρ ×id))
  reindexExtension α ρ = isFibExt λ _ _ _ _ _ → refl
