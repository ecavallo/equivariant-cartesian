{-

Fibrancy of extension types.

-}
module type-formers.extension where

open import prelude
open import axioms
open import fibration.fibration

private variable
  ℓ : Level
  Γ Δ : Type ℓ

-- TODO do something better with this
Partial : (Z : Shape) (φ : ⟨ Z ⟩ → Cof)
  (A : Γ ▷⟨ Z ⟩ → Type ℓ)
  → Γ → Type ℓ
Partial Z φ A γ = ∀ z → [ φ z ] → A (γ , z)

Extensionᴵ : (Z : Shape)
  (A : Γ ▷⟨ Z ⟩ → Type ℓ)
  (φ : ⟨ Z ⟩ → Cof)
  (a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ snd ] ⊢ A ∘ wk[ φ ∘ snd ])
  → Γ → Type ℓ
Extensionᴵ Z A φ a γ =
  (z : ⟨ Z ⟩) → A (γ , z) [ φ z ↦ curry a (γ , z) ]

module ExtensionLift {Z φ S r}
  {A : ⟨ S ⟩ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
  {a : ⟨ S ⟩ ▷⟨ Z ⟩ ▷[ φ ∘ snd ] ⊢ A ∘ wk[ φ ∘ snd ]}
  (box : OpenBox S r (Extensionᴵ Z A φ a))
  where

  module _ (z : ⟨ Z ⟩) where

    boxA : OpenBox S r (λ s → A (s , z))
    boxA .cof = box .cof ∨ φ z
    boxA .tube s =
      ∨-rec (box .cof) (φ z)
        (λ u → box .tube s u z .out)
        (λ v → a (s , z , v))
        (λ u v → sym (box .tube s u z .out≡ v))
    boxA .cap .out = box .cap .out z .out
    boxA .cap .out≡ =
      ∨-elimEq (box .cof) (φ z)
        (λ u → cong (λ q → q z .out) (box .cap .out≡ u))
        (λ v → box .cap .out z .out≡ v)

    fillA = α .lift S r (_, z) boxA

  filler : Filler box
  filler .fill s .out z .out = fillA z .fill s .out
  filler .fill s .out z .out≡ v = fillA z .fill s .out≡ (∨r v)
  filler .fill s .out≡ u = funExt λ z → restrictExt (fillA z .fill s .out≡ (∨l u))
  filler .cap≡ = funExt λ z → restrictExt (fillA z .cap≡)

module ExtensionVary {Z φ S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
  {a : ⟨ T ⟩ ▷⟨ Z ⟩ ▷[ φ ∘ snd ] ⊢ A ∘ wk[ φ ∘ snd ]}
  (box : OpenBox T (⟪ σ ⟫ r) (Extensionᴵ Z A φ a))
  where

  module T = ExtensionLift α box
  module S = ExtensionLift (α ∘ᶠˢ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    funExt λ z →
    restrictExt
      (α .vary S T σ r (_, z) (T.boxA z) s
        ∙ cong (λ b → α .lift S r ((_, z) ∘ ⟪ σ ⟫) b .fill s .out)
            (boxExt refl
              (λ _ →
                diagonalCofElim (box .cof ∨ φ z) $
                ∨-elimEq (box .cof) (φ z) (λ _ → refl) (λ _ → refl))
              refl))

opaque
  ExtensionFibStr : (Z : Shape)
    {A : Γ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
    (φ : ⟨ Z ⟩ → Cof)
    (a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ snd ] ⊢ A ∘ wk[ φ ∘ snd ])
    → FibStr (Extensionᴵ Z A φ a)
  ExtensionFibStr Z α φ a .lift S r p = ExtensionLift.filler (α ∘ᶠˢ (p ×id))
  ExtensionFibStr Z α φ a .vary S T σ r p = ExtensionVary.eq σ (α ∘ᶠˢ (p ×id))

  ----------------------------------------------------------------------------------------
  -- Forming extension types is stable under reindexing
  ----------------------------------------------------------------------------------------
  reindexExtensionFibStr : {Z : Shape}
    {A : Γ ▷⟨ Z ⟩ → Type ℓ} {α : FibStr A}
    {φ : ⟨ Z ⟩ → Cof}
    {a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ snd ] ⊢ A ∘ wk[ φ ∘ snd ]}
    (ρ : Δ → Γ)
    → ExtensionFibStr Z α φ a ∘ᶠˢ ρ
      ≡ ExtensionFibStr Z (α ∘ᶠˢ ρ ×id) φ (a ∘ ρ ×id ×id)
  reindexExtensionFibStr ρ = FibStrExt λ _ _ _ _ _ → refl

Extensionᶠ : (Z : Shape) (A : Γ ▷⟨ Z ⟩ ⊢ᶠType ℓ) (φ : ⟨ Z ⟩ → Cof)
  (a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ snd ] ⊢ᶠ A ∘ᶠ wk[ φ ∘ snd ])
  → Γ ⊢ᶠType ℓ
Extensionᶠ Z A φ a .fst = Extensionᴵ Z (A .fst) φ a
Extensionᶠ Z A φ a .snd = ExtensionFibStr Z (A .snd) φ a
