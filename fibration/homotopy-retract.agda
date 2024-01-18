{-

  A fiberwise-fibrant homotopy retract of a fibration is a fibration.

-}
module fibration.homotopy-retract where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.coercion
open import fibration.fibration
open import type-former.path

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

hRetract : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
hRetract A B = Σ f ∈ (A → B) , Σ g ∈ (B → A) , ∀ a → g (f a) ~ a

hRetractˣ : (Γ → Type ℓ) → (Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
hRetractˣ A B γ = hRetract (A γ) (B γ)

module hRetractLift {S r}
  {A : ⟨ S ⟩ → Type ℓ} (α : ∀ i → FibStr {Γ = 𝟙} (A ∘ cst i))
  {B : ⟨ S ⟩ → Type ℓ'} (β : FibStr B)
  (f : ⟨ S ⟩ ⊢ˣ hRetractˣ A B)
  (box : OpenBox S A r)
  where

  codBox : OpenBox S B r
  codBox = mapBox (fst ∘ f) box

  codFiller : Filler codBox
  codFiller = β .lift S id r codBox

  retractedFiller : Filler (mapBox (fst ∘ snd ∘ f) codBox)
  retractedFiller = mapFiller (fst ∘ snd ∘ f) codFiller

  correctorBox : (s : ⟨ S ⟩) → OpenBox 𝕚 (cst (A s)) 0
  correctorBox s .cof =
    box .cof ∨ S ∋ r ≈ s
  correctorBox s .tube i u =
    f s .snd .snd (boxToPartial box s u) .at i
  correctorBox s .cap .out = retractedFiller .fill s .out
  correctorBox s .cap .out≡ =
    ∨-elimEq
      (λ u →
        f s .snd .snd (boxToPartial box s (∨l u)) .at0
        ∙ retractedFiller .fill s .out≡ u)
      (λ {refl →
        f s .snd .snd (boxToPartial box s (∨r refl)) .at0
        ∙ sym (retractedFiller .cap≡)})

  correctorFiller : (s : ⟨ S ⟩) → Filler (correctorBox s)
  correctorFiller s = α s .lift 𝕚 _ 0 (correctorBox s)

  opaque
    filler : Filler box
    filler =
      fitsPartialToFiller total
      where
      total : ∀ s → A s [ box .cof ∨ (S ∋ r ≈ s) ↦ boxToPartial box s ]
      total s .out = correctorFiller s .fill 1 .out
      total s .out≡ uv =
        sym (f s .snd .snd (boxToPartial box s uv) .at1)
        ∙ correctorFiller s .fill 1 .out≡ uv

module hRetractVary {S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ → Type ℓ} (α : ∀ i → FibStr {Γ = 𝟙} (A ∘ cst i))
  {B : ⟨ T ⟩ → Type ℓ'} (β : FibStr B)
  (f : ⟨ T ⟩ ⊢ˣ hRetractˣ A B)
  (box : OpenBox T A (⟪ σ ⟫ r))
 where

  module T = hRetractLift α β f box
  module S = hRetractLift (α ∘ ⟪ σ ⟫) (β ∘ᶠˢ ⟪ σ ⟫) (f ∘ ⟪ σ ⟫) (reshapeBox σ box)

  opaque
    unfolding hRetractLift.filler
    eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
    eq s =
      cong
        (λ box' → α (⟪ σ ⟫ s) .lift 𝕚 _ 𝕚0 box' .fill 𝕚1 .out)
        (boxExt
          (cong (box .cof ∨_) (≈Equivariant σ r s))
          (λ i →
            takeOutCof (box .cof) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
              (λ u → refl)
              (λ {refl refl → refl}))
          (cong (f _ .snd .fst) (β .vary S T σ id r (mapBox (fst ∘ f) box) s)))


hRetractFibStr :
  {A : Γ → Type ℓ} (α : ∀ γ → FibStr {Γ = 𝟙} (A ∘ cst γ))
  {B : Γ → Type ℓ'} (β : FibStr B)
  (f : Γ ⊢ˣ hRetractˣ A B)
  → FibStr A
hRetractFibStr α β f .lift S p r box =
  hRetractLift.filler (α ∘ p) (β ∘ᶠˢ p) (f ∘ p) box
hRetractFibStr α β f .vary S T σ p r box =
  hRetractVary.eq σ (α ∘ p) (β ∘ᶠˢ p) (f ∘ p) box
