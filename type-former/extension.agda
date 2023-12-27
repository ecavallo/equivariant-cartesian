{-

Fibrancy of extension types.

-}
module type-former.extension where

open import prelude
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ : Level
  Γ Δ : Type ℓ

-- TODO do something better with this
Partial : (Z : Shape) (φ : ⟨ Z ⟩ → Cof)
  (A : Γ ▷⟨ Z ⟩ → Type ℓ)
  → Γ → Type ℓ
Partial Z φ A γ = ∀ z → [ φ z ] → A (γ , z)

Extensionˣ : (Z : Shape)
  (A : Γ ▷⟨ Z ⟩ → Type ℓ)
  (φ : ⟨ Z ⟩ → Cof)
  (a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ 𝒒 ] ⊢ˣ A ↾ (φ ∘ 𝒒))
  → Γ → Type ℓ
Extensionˣ Z A φ a γ =
  (z : ⟨ Z ⟩) → A (γ , z) [ φ z ↦ curry a (γ , z) ]

module ExtensionLift {Z φ S r}
  {A : ⟨ S ⟩ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
  {a : ⟨ S ⟩ ▷⟨ Z ⟩ ▷[ φ ∘ 𝒒 ] ⊢ˣ A ↾ (φ ∘ 𝒒)}
  (box : OpenBox S r (Extensionˣ Z A φ a))
  where

  module _ (z : ⟨ Z ⟩) where

    pointwiseBox : OpenBox S r (λ s → A (s , z))
    pointwiseBox =
      addToTube
        (mapBox (λ _ q → q z .out) box)
        (φ z)
        (λ i v → λ where
          .out → a (i , z , v)
          .out≡ u → sym (box .tube i u z .out≡ v))
        (λ v → box .cap .out z .out≡ v)

    pointwiseFill = α .lift S r (_, z) pointwiseBox

  filler : Filler box
  filler .fill s .out z .out = pointwiseFill z .fill s .out
  filler .fill s .out z .out≡ v = pointwiseFill z .fill s .out≡ (∨r v)
  filler .fill s .out≡ u =
    funExt λ z → restrictExt (pointwiseFill z .fill s .out≡ (∨l u))
  filler .cap≡ = funExt λ z → restrictExt (pointwiseFill z .cap≡)

module ExtensionVary {Z φ S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
  {a : ⟨ T ⟩ ▷⟨ Z ⟩ ▷[ φ ∘ 𝒒 ] ⊢ˣ A ↾ (φ ∘ 𝒒)}
  (box : OpenBox T (⟪ σ ⟫ r) (Extensionˣ Z A φ a))
  where

  module T = ExtensionLift α box
  module S = ExtensionLift (α ∘ᶠˢ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    funExt λ z →
    restrictExt $
    α .vary S T σ r (_, z) (T.pointwiseBox z) s
    ∙ cong (λ b → α .lift S r ((_, z) ∘ ⟪ σ ⟫) b .fill s .out)
        (boxExt refl
          (λ _ →
            diagonalCofElim (box .cof ∨ φ z) $
            ∨-elimEq (λ _ → refl) (λ _ → refl))
          refl)

opaque
  ExtensionFibStr : (Z : Shape)
    {A : Γ ▷⟨ Z ⟩ → Type ℓ} (α : FibStr A)
    (φ : ⟨ Z ⟩ → Cof)
    (a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ 𝒒 ] ⊢ˣ A ↾ (φ ∘ 𝒒))
    → FibStr (Extensionˣ Z A φ a)
  ExtensionFibStr Z α φ a .lift S r p = ExtensionLift.filler (α ∘ᶠˢ (p ×id))
  ExtensionFibStr Z α φ a .vary S T σ r p = ExtensionVary.eq σ (α ∘ᶠˢ (p ×id))

  ----------------------------------------------------------------------------------------
  -- Forming extension types is stable under reindexing
  ----------------------------------------------------------------------------------------
  reindexExtensionFibStr : {Z : Shape}
    {A : Γ ▷⟨ Z ⟩ → Type ℓ} {α : FibStr A}
    {φ : ⟨ Z ⟩ → Cof}
    {a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ 𝒒 ] ⊢ˣ A ↾ (φ ∘ 𝒒)}
    (ρ : Δ → Γ)
    → ExtensionFibStr Z α φ a ∘ᶠˢ ρ
      ≡ ExtensionFibStr Z (α ∘ᶠˢ ρ ×id) φ (a ∘ ρ ×id ×id)
  reindexExtensionFibStr ρ = FibStrExt λ _ _ _ _ _ → refl

Extensionᶠ : (Z : Shape) (A : Γ ▷⟨ Z ⟩ ⊢ᶠType ℓ) (φ : ⟨ Z ⟩ → Cof)
  (a : Γ ▷⟨ Z ⟩ ▷[ φ ∘ 𝒒 ] ⊢ᶠ A ↾ᶠ (φ ∘ 𝒒))
  → Γ ⊢ᶠType ℓ
Extensionᶠ Z A φ a .fst = Extensionˣ Z (A .fst) φ a
Extensionᶠ Z A φ a .snd = ExtensionFibStr Z (A .snd) φ a
