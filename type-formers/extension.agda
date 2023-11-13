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
  (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
  (S : Shape)
  {A : ⟨ S ⟩ × ⟨ Z ⟩ → Set ℓ}
  (α : isFib A)
  {a : ∀ s z → [ Φ z ] → A (s , z)}
  (r : ⟨ S ⟩) (box : OpenBox S r (λ s → (Extension' Z Φ A (s , a s))))
  where

  module _ (z : ⟨ Z ⟩) where

    boxA : OpenBox S r (λ s → A (s , z))
    boxA .cof = box .cof ∨ Φ z
    boxA .tube =
      ∨-rec (box .cof) (Φ z)
        (λ u s → box .tube u s z .fst)
        (λ v s → a s z v)
        (λ u v → funext λ s → symm (box .tube u s z .snd v))
    boxA .cap .fst = box .cap .fst z .fst
    boxA .cap .snd =
      ∨-elimEq (box .cof) (Φ z)
        (λ u → cong (λ q → q z .fst) (box .cap .snd u))
        (λ v → box .cap .fst z .snd v)

    fillA = α .lift S r (_, z) boxA

opaque
  ExtensionIsFib :
    ∀ {ℓ ℓ'} (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
    {Γ : Set ℓ}
    {A : Γ × ⟨ Z ⟩ → Set ℓ'}
    (α : isFib A)
    → isFib (Extension' Z Φ A)
  ExtensionIsFib Z Φ {A = A} α .lift S r p box .fill s .fst z =
    fillA z .fill s .fst , λ v → fillA z .fill s .snd ∣ inr v ∣
    where
    open ExtensionIsFibId Z Φ S (reindex A α ((fst ∘ p) ×id)) r box

  ExtensionIsFib Z Φ {A = A} α .lift S r p box .fill s .snd u =
    funext λ z →
    Σext (fillA z .fill s .snd ∣ inl u ∣) (funext λ _ → uipImp)
    where
    open ExtensionIsFibId Z Φ S (reindex A α ((fst ∘ p) ×id)) r box

  ExtensionIsFib Z Φ {A = A} α .lift S r p box .cap≡ =
    funext λ z →
    Σext (fillA z .cap≡) (funext λ _ → uipImp)
    where
    open ExtensionIsFibId Z Φ S (reindex A α ((fst ∘ p) ×id)) r box

  ExtensionIsFib Z Φ {A = A} α .vary S T σ r p box s =
    funext λ z →
    Σext
      (α .vary S T σ r (((fst ∘ p) ×id) ∘ (_, z)) (T.boxA z) s
        ∙ cong (λ b → α .lift S r ((fst ∘ p ∘ ⟪ σ ⟫) ×id ∘ (_, z)) b .fill s .fst)
            (boxExt refl
              (diagonalElim (box .cof ∨ Φ z)
                (∨-elimEq (box .cof) (Φ z) (λ _ → refl) (λ _ → refl)))
              refl))
      (funext λ _ → uipImp)
    where
    module T = ExtensionIsFibId Z Φ T (reindex A α ((fst ∘ p) ×id)) (⟪ σ ⟫ r) box
    module S = ExtensionIsFibId Z Φ S (reindex A α ((fst ∘ p ∘ ⟪ σ ⟫) ×id)) r (reshapeBox σ box)

  ----------------------------------------------------------------------
  -- Forming extension types is stable under reindexing
  ----------------------------------------------------------------------
  reindexExtension :
    ∀ {ℓ ℓ' ℓ''} (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ × ⟨ Z ⟩ → Set ℓ'')
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Extension' Z Φ A) (ExtensionIsFib Z Φ α) (ρ ×id) ≡ ExtensionIsFib Z Φ (reindex A α (ρ ×id))
  reindexExtension Z Φ A α ρ = isFibExt λ _ _ _ _ _ → refl
