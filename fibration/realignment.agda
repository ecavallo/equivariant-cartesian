{-

Realign a fibration structure to agree with another on some cofibration

-}
{-# OPTIONS --rewriting #-}
module fibration.realignment where

open import prelude
open import axioms
open import fibration.fibration

private variable
  ℓ : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Realigning a fibration structure on a given family
------------------------------------------------------------------------------------------

module RealignLift {S r} (φ : ⟨ S ⟩ → CofProp)
  {B : ⟨ S ⟩ → Type ℓ}
  (β : FibStr B)
  (α : FibStr (B ∘ wk[ φ ]))
  (box : OpenBox S r B)
  where

  fillA : [ all S φ ] → _
  fillA u = α .lift S r (id ,, u) box

  box' : OpenBox S r B
  box' .cof = box .cof ∨ all S φ
  box' .tube =
    ∨-rec (box .cof) (all S φ)
      (box .tube)
      (λ u i → fillA u .fill i .out)
      (λ v u → funext λ i → fillA u .fill i .out≡ v)
  box' .cap .out = box .cap .out
  box' .cap .out≡ =
    ∨-elimEq (box .cof) (all S φ)
      (box .cap .out≡)
      (λ u → fillA u .cap≡)

  fillB = β .lift S r id box'

  filler : Filler box
  filler .fill s .out = fillB .fill s .out
  filler .fill s .out≡ v = fillB .fill s .out≡ (∨l v)
  filler .cap≡ = fillB .cap≡

module RealignVary {S T} (σ : ShapeHom S T) {r}
  (φ : ⟨ T ⟩ → CofProp)
  {B : ⟨ T ⟩ → Type ℓ}
  (β : FibStr B)
  (α : FibStr (B ∘ wk[ φ ]))
  (box : OpenBox T (⟪ σ ⟫ r) B)
  where

  module T = RealignLift φ β α box
  module S =
    RealignLift (φ ∘ ⟪ σ ⟫)
      (β ∘ᶠˢ ⟪ σ ⟫) (α ∘ᶠˢ ⟪ σ ⟫ ×id) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    β .vary S T σ r id T.box' s
    ∙
    cong
      (λ box' → β .lift S r ⟪ σ ⟫ box' .fill s .out)
      (boxExt
        (cong (λ φ → box .cof ∨ φ) (allEquivariant σ φ))
        (takeOutCof (box .cof) (all T φ) (all S (φ ∘ ⟪ σ ⟫))
          (λ _ → refl)
          (λ uS uT → funext λ i →
            α .vary S T σ r (id ,, uS) box i
            ∙ cong (λ w → α .lift S r (⟪ σ ⟫ ,, w) (reshapeBox σ box) .fill i .out)
              (funext λ s → cofIsProp (φ (⟪ σ ⟫ s)) _ _)))
        refl)

opaque
  realignFibStr : (φ : Γ → CofProp)
    {B : Γ → Type ℓ}
    (β : FibStr B)
    (α : FibStr (B ∘ wk[ φ ]))
    → FibStr B
  realignFibStr φ β α .lift S r p =
    RealignLift.filler (φ ∘ p) (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id)
  realignFibStr φ β α .vary S T σ r p =
    RealignVary.eq σ (φ ∘ p) (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id)

  -- TODO prove this in RealignLift?
  isRealigned : (φ : Γ → CofProp)
    {B : Γ → Type ℓ}
    (β : FibStr B)
    (α : FibStr (B ∘ wk[ φ ]))
    → α ≡ realignFibStr φ β α ∘ᶠˢ fst
  isRealigned φ β α =
    FibStrExt λ S r p box s →
      RealignLift.fillB _ (β ∘ᶠˢ (wk[ φ ] ∘ p)) (α ∘ᶠˢ (wk[ φ ] ∘ p) ×id) _
      .fill s .out≡ (∨r (snd ∘ p))

  reindexRealignFibStr : (φ : Γ → CofProp)
    {B : Γ → Type ℓ}
    (β : FibStr B)
    (α : FibStr (B ∘ wk[ φ ]))
    (ρ : Δ → Γ)
    → realignFibStr φ β α ∘ᶠˢ ρ
    ≡ realignFibStr (φ ∘ ρ) (β ∘ᶠˢ ρ) (α ∘ᶠˢ ρ ×id)
  reindexRealignFibStr φ β α ρ = FibStrExt λ S r p box s → refl

------------------------------------------------------------------------------------------
-- Realigning a fibration
------------------------------------------------------------------------------------------

opaque
  ≅Realignᶠ : (φ : Γ → CofProp)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ A .fst ≅ᴵ (B .fst ∘ fst))
    → Γ ⊢ᶠType ℓ
  ≅Realignᶠ φ _ _ iso .fst γ = ≅Realign (φ γ) _ _ (iso ∘ (γ ,_))
  ≅Realignᶠ φ (_ , β) (_ , α) iso .snd =
    realignFibStr φ
      (isomorphFibStr (λ γ → ≅realign (φ γ) _ _ (iso ∘ (γ ,_))) β)
      (subst FibStr (funext (uncurry λ γ → ≅RealignMatch (φ γ) _ _ (iso ∘ (γ ,_)))) α)

  ≅RealignᶠMatch : (φ : Γ → CofProp)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ A .fst ≅ᴵ (B .fst ∘ fst))
    → A ≡ ≅Realignᶠ φ B A iso ∘ᶠ fst
  ≅RealignᶠMatch _ _ _ _ =
    Σext _ (isRealigned _ _ _)

  ≅realignᶠ : (φ : Γ → CofProp)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ A .fst ≅ᴵ (B .fst ∘ fst))
    → Γ ⊢ ≅Realignᶠ φ B A iso .fst ≅ᴵ B .fst
  ≅realignᶠ φ B A iso γ = ≅realign _ _ _ _

  reindexRealignᶠ : (φ : Γ → CofProp)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ A .fst ≅ᴵ (B .fst ∘ fst))
    (ρ : Δ → Γ)
    → ≅Realignᶠ φ B A iso ∘ᶠ ρ ≡ ≅Realignᶠ (φ ∘ ρ) (B ∘ᶠ ρ) (A ∘ᶠ ρ ×id) (iso ∘ ρ ×id)
  reindexRealignᶠ φ (_ , β) (_ , α) iso ρ =
    Σext refl
      (reindexRealignFibStr _ _ _ ρ
        ∙ cong₂ (realignFibStr (φ ∘ ρ))
            (reindexIsomorphFibStr (λ _ → ≅realign _ _ _ _) _ ρ)
            (reindexSubst (ρ ×id) _ _ α))
