{-

Fibrancy of extension types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.extension where

open import prelude
open import axioms
open import fibration.fibration

private variable
  ℓ : Level
  Γ Δ : Type ℓ

-- TODO do something better with this
Partial : (Z : Shape) (Φ : ⟨ Z ⟩ → CofProp)
  (A : Γ ▷⟨ Z ⟩ → Type ℓ)
  → Γ → Type ℓ
Partial Z Φ A γ = ∀ z → [ Φ z ] → A (γ , z)

Extensionᴵ : (Z : Shape)
  (A : Γ ▷⟨ Z ⟩ → Type ℓ)
  (Φ : ⟨ Z ⟩ → CofProp)
  (a : Γ ▷⟨ Z ⟩ ▷[ Φ ∘ snd ] ⊢ A ∘ wk[ Φ ∘ snd ])
  → Γ → Type ℓ
Extensionᴵ Z A Φ a γ =
  (z : ⟨ Z ⟩) → A (γ , z) [ Φ z ↦ curry a (γ , z) ]

module ExtensionLift {Z Φ S r}
  {A : ⟨ S ⟩ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
  {a : ⟨ S ⟩ ▷⟨ Z ⟩ ▷[ Φ ∘ snd ] ⊢ A ∘ wk[ Φ ∘ snd ]}
  (box : OpenBox S r (Extensionᴵ Z A Φ a))
  where

  module _ (z : ⟨ Z ⟩) where

    boxA : OpenBox S r (λ s → A (s , z))
    boxA .cof = box .cof ∨ Φ z
    boxA .tube =
      ∨-rec (box .cof) (Φ z)
        (λ u s → box .tube u s z .out)
        (λ v s → a ((s , z) , v))
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
  {A : ⟨ T ⟩ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
  {a : ⟨ T ⟩ ▷⟨ Z ⟩ ▷[ Φ ∘ snd ] ⊢ A ∘ wk[ Φ ∘ snd ]}
  (box : OpenBox T (⟪ σ ⟫ r) (Extensionᴵ Z A Φ a))
  where

  module T = ExtensionLift α box
  module S = ExtensionLift (α ∘ᶠˢ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

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
  ExtensionFibStr : (Z : Shape)
    {A : Γ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
    (Φ : ⟨ Z ⟩ → CofProp)
    (a : Γ ▷⟨ Z ⟩ ▷[ Φ ∘ snd ] ⊢ A ∘ wk[ Φ ∘ snd ])
    → FibStr (Extensionᴵ Z A Φ a)
  ExtensionFibStr Z α Φ a .lift S r p = ExtensionLift.filler (α ∘ᶠˢ (p ×id))
  ExtensionFibStr Z α Φ a .vary S T σ r p = ExtensionVary.eq σ (α ∘ᶠˢ (p ×id))

  ----------------------------------------------------------------------------------------
  -- Forming extension types is stable under reindexing
  ----------------------------------------------------------------------------------------
  reindexExtensionFibStr : {Z : Shape}
    {A : Γ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
    {Φ : ⟨ Z ⟩ → CofProp}
    {a : Γ ▷⟨ Z ⟩ ▷[ Φ ∘ snd ] ⊢ A ∘ wk[ Φ ∘ snd ]}
    (ρ : Δ → Γ)
    → ExtensionFibStr Z α Φ a ∘ᶠˢ ρ
      ≡ ExtensionFibStr Z (α ∘ᶠˢ ρ ×id) Φ (a ∘ ρ ×id ×id)
  reindexExtensionFibStr α ρ = FibStrExt λ _ _ _ _ _ → refl

Extensionᶠ : (Z : Shape)
  (A : Γ ▷⟨ Z ⟩ ⊢ᶠType ℓ)
  (Φ : ⟨ Z ⟩ → CofProp)
  (a : Γ ▷⟨ Z ⟩ ▷[ Φ ∘ snd ] ⊢ᶠ A ∘ᶠ wk[ Φ ∘ snd ])
  → Γ ⊢ᶠType ℓ
Extensionᶠ Z A Φ a .fst = Extensionᴵ Z (A .fst) Φ a
Extensionᶠ Z A Φ a .snd = ExtensionFibStr Z (A .snd) Φ a
