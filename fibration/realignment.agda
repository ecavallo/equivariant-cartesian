{-

Realignment for fibrations along cofibrations.

First we prove that the notion of fibration is /relatively acyclic/. We use this in
combination with realignment for the internal extensional type theory (see
axiom.realignment) to prove realignment for fibrations.

-}
module fibration.realignment where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Relative acyclicity, i.e. realigning fibration structures.
--
-- Given
--
-- ∘ a fibration B over Γ,
-- ∘ a cofibration φ over Γ,
-- ∘ a "partial" fibration structure α on the restricted family B ↾ φ over Γ ▷[ φ ] ,
--
-- there exists a fibration structure on B that restricts on φ to α.
------------------------------------------------------------------------------------------

--↓ Construction of lifts on for the realigned fibration structure.

module RealignLift {S r} (φ : ⟨ S ⟩ → Cof)
  {B : ⟨ S ⟩ → Type ℓ} (β : FibStr B)
  (α : FibStr (B ↾ φ))
  (box : OpenBox S r B)
  where

  --↓ First, use the partial fibration structure to construct a lift when the cofibration
  --↓ ∀φ holds.

  fillPartial : [ all S φ ] → Filler box
  fillPartial u = α .lift S r (id ,, u) box

  --↓ Use the total fibration structure to construct a lift for the original box that
  --↓ also agrees on ∀φ with the partial lift just construction.

  boxTotal : OpenBox S r B
  boxTotal =
    addToTube
      box
      (all S φ)
      (λ i u → fillPartial u .fill i)
      (λ v → fillPartial v .cap≡)

  fillTotal = β .lift S r id boxTotal

  --↓ Extract a filler for the original lifting problem

  filler : Filler box
  filler .fill s .out = fillTotal .fill s .out
  filler .fill s .out≡ v = fillTotal .fill s .out≡ (∨l v)
  filler .cap≡ = fillTotal .cap≡

--↓ Proof that the lifts satisfy the equivariance condition.
--↓ This proof relies on the invariance of ∀ under shape homomorphisms, i.e., that for
--↓ any shape homorphism σ : S → T the cofibrations ∀t:T.φ(t) and ∀s:S.φ(σ(s)) are equal.

module RealignVary {S T} (σ : ShapeHom S T) {r}
  (φ : ⟨ T ⟩ → Cof)
  {B : ⟨ T ⟩ → Type ℓ} (β : FibStr B)
  (α : FibStr (B ↾ φ))
  (box : OpenBox T (⟪ σ ⟫ r) B)
  where

  module T = RealignLift φ β α box
  module S = RealignLift (φ ∘ ⟪ σ ⟫) (β ∘ᶠˢ ⟪ σ ⟫) (α ∘ᶠˢ ⟪ σ ⟫ ×id) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    β .vary S T σ r id T.boxTotal s
    ∙
    cong
      (λ box' → β .lift S r ⟪ σ ⟫ box' .fill s .out)
      (boxExt
        (cong (box .cof ∨_) (allEquivariant σ φ))
        (λ i → takeOutCof (box .cof) (all T φ) (all S (φ ∘ ⟪ σ ⟫))
          (λ _ → refl)
          (λ uS uT →
            α .vary S T σ r (id ,, uS) box i
            ∙ cong (λ w → α .lift S r (⟪ σ ⟫ ,, w) (reshapeBox σ box) .fill i .out)
              (funExt λ s → cofIsStrictProp' (φ (⟪ σ ⟫ s)))))
        refl)

opaque
  --↓ Definition of the realigned fibration structure.

  realignFibStr : (φ : Γ → Cof)
    {B : Γ → Type ℓ} (β : FibStr B)
    (α : FibStr (B ↾ φ))
    → FibStr B
  realignFibStr φ β α .lift S r p =
    RealignLift.filler (φ ∘ p) (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id)
  realignFibStr φ β α .vary S T σ r p =
    RealignVary.eq σ (φ ∘ p) (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id)

  --↓ Proof that the realigned fibration structure indeed restricts to the given partial
  --↓ fibration structure.

  realignFibStrMatch : (φ : Γ → Cof)
    {B : Γ → Type ℓ} (β : FibStr B)
    (α : FibStr (B ↾ φ))
    → α ≡ realignFibStr φ β α ∘ᶠˢ 𝒑
  realignFibStrMatch φ β α =
    FibStrExt λ S r p box s →
      RealignLift.fillTotal _ ((β ↾ᶠˢ φ) ∘ᶠˢ p) (α ∘ᶠˢ ((𝒑 ∘ p) ×id)) _
      .fill s .out≡ (∨r (𝒒 ∘ p))

  --↓ Realignment commutes with reindexing of fibrations.

  reindexRealignFibStr : {φ : Γ → Cof}
    {B : Γ → Type ℓ} {β : FibStr B}
    {α : FibStr (B ↾ φ)}
    (ρ : Δ → Γ)
    → realignFibStr φ β α ∘ᶠˢ ρ ≡ realignFibStr (φ ∘ ρ) (β ∘ᶠˢ ρ) (α ∘ᶠˢ ρ ×id)
  reindexRealignFibStr ρ = FibStrExt λ S r p box s → refl

------------------------------------------------------------------------------------------
-- Realignment for fibrations along cofibrations.
--
-- Given
--
-- ∘ a "total" fibration B over Γ,
-- ∘ a cofibration φ over Γ,
-- ∘ a "partial" fibration A over the restricted context Γ ▷[ φ ] such that A is
--   (strictly) isomorphic to B ↾ φ,
--
-- there exists a fibration over Γ that is (strictly) isomorphic to B and restricts on φ
-- to A (up to strict equality).
------------------------------------------------------------------------------------------

opaque
  --↓ Construction of the realigned fibration.

  ≅Realignᶠ : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ ∣ A ∣ ≅ˣ ∣ B ↾ᶠ φ ∣)
    → Γ ⊢ᶠType ℓ
  ≅Realignᶠ φ _ _ iso .fst γ = ≅Realign (φ γ) (iso ∘ (γ ,_))
  ≅Realignᶠ φ (_ , β) (_ , α) iso .snd =
    realignFibStr φ
      (isomorphFibStr (λ γ → ≅realign (φ γ) (iso ∘ (γ ,_))) β)
      (subst FibStr (funExt (uncurry λ γ → ≅RealignMatch (φ γ) (iso ∘ (γ ,_)))) α)

  --↓ Proof that the realigned fibration restricts to the input partial fibration.

  ≅RealignᶠMatch : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ ∣ A ∣ ≅ˣ ∣ B ↾ᶠ φ ∣)
    → A ≡ ≅Realignᶠ φ B A iso ↾ᶠ φ
  ≅RealignᶠMatch _ _ _ _ =
    Σext _ (realignFibStrMatch _ _ _)

  --↓ Isomorphism from the input total fibration to the realigned fibration.

  ≅realignᶠ : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ ∣ A ∣ ≅ˣ ∣ B ↾ᶠ φ ∣)
    → Γ ⊢ˣ ≅Realignᶠ φ B A iso .fst ≅ˣ B .fst
  ≅realignᶠ φ B A iso γ = ≅realign _ _

  --↓ Proof that the isomorphism above restricts to the input isomorphism.

  ≅realignᶠMatch : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ ∣ A ∣ ≅ˣ ∣ B ↾ᶠ φ ∣)
    → subst (λ C → Γ ▷[ φ ] ⊢ˣ ∣ C ∣ ≅ˣ ∣ B ↾ᶠ φ ∣) (≅RealignᶠMatch φ B A iso) iso
      ≡ ≅realignᶠ φ B A iso ↾ φ
  ≅realignᶠMatch φ B A iso =
    funExt λ (γ , u) →
    substNaturality {B = λ C → _ ⊢ˣ ∣ C ∣ ≅ˣ ∣ B ↾ᶠ φ ∣} (_$ (γ , u))
      (≅RealignᶠMatch φ B A iso)
    ∙ substCongAssoc (λ C → C ≅ B $ᶠ γ) (_$ᶠ (γ , u)) (≅RealignᶠMatch φ B A iso) _
    ∙ cong (subst (_≅ B $ᶠ γ) ⦅–⦆ (iso (γ , u))) uip'
    ∙ ≅realignMatch (φ γ) (iso ∘ (γ ,_)) u

  --↓ Realignment commmutes with reindexing.

  reindexRealignᶠ : {φ : Γ → Cof}
    {B : Γ ⊢ᶠType ℓ}
    {A : Γ ▷[ φ ] ⊢ᶠType ℓ}
    {iso : Γ ▷[ φ ] ⊢ˣ ∣ A ∣ ≅ˣ ∣ B ↾ᶠ φ ∣}
    (ρ : Δ → Γ)
    → ≅Realignᶠ φ B A iso ∘ᶠ ρ ≡ ≅Realignᶠ (φ ∘ ρ) (B ∘ᶠ ρ) (A ∘ᶠ ρ ×id) (iso ∘ ρ ×id)
  reindexRealignᶠ {A = _ , α} ρ =
    Σext refl
      (reindexRealignFibStr _
        ∙ cong₂ (realignFibStr _)
            (reindexIsomorphFibStr (λ _ → ≅realign _ _) _)
            (reindexSubst α _ _ _))
