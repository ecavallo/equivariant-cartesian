{-

Realign a fibration structure to agree with another on some cofibration

TODO: package with Type-realignment to get a proof that fibrations (not just their structures) can be
realigned

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
  {A : ⟨ S ⟩ → Type ℓ}
  (β : FibStr (A ∘ wk[ φ ]))
  (α : FibStr A)
  (box : OpenBox S r A)
  where

  fillB : [ all S φ ] → _
  fillB u = β .lift S r (id ,, u) box

  box' : OpenBox S r A
  box' .cof = box .cof ∨ all S φ
  box' .tube =
    ∨-rec (box .cof) (all S φ)
      (box .tube)
      (λ u i → fillB u .fill i .out)
      (λ v u → funext λ i → fillB u .fill i .out≡ v)
  box' .cap .out = box .cap .out
  box' .cap .out≡ =
    ∨-elimEq (box .cof) (all S φ)
      (box .cap .out≡)
      (λ u → fillB u .cap≡)

  fillA = α .lift S r id box'

  filler : Filler box
  filler .fill s .out = fillA .fill s .out
  filler .fill s .out≡ v = fillA .fill s .out≡ (∨l v)
  filler .cap≡ = fillA .cap≡

module RealignVary {S T} (σ : ShapeHom S T) {r}
  (φ : ⟨ T ⟩ → CofProp)
  {A : ⟨ T ⟩ → Type ℓ}
  (β : FibStr (A ∘ wk[ φ ]))
  (α : FibStr A)
  (box : OpenBox T (⟪ σ ⟫ r) A)
  where

  module T = RealignLift φ β α box
  module S =
    RealignLift (φ ∘ ⟪ σ ⟫)
      (β ∘ᶠˢ ⟪ σ ⟫ ×id) (α ∘ᶠˢ ⟪ σ ⟫) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    α .vary S T σ r id T.box' s
    ∙
    cong
      (λ box' → α .lift S r ⟪ σ ⟫ box' .fill s .out)
      (boxExt
        (cong (λ φ → box .cof ∨ φ) (allEquivariant σ φ))
        (takeOutCof (box .cof) (all T φ) (all S (φ ∘ ⟪ σ ⟫))
          (λ _ → refl)
          (λ uS uT → funext λ i →
            β .vary S T σ r (id ,, uS) box i
            ∙ cong (λ w → β .lift S r (⟪ σ ⟫ ,, w) (reshapeBox σ box) .fill i .out)
              (funext λ s → cofIsProp (φ (⟪ σ ⟫ s)) _ _)))
        refl)

opaque
  realignFibStr : (φ : Γ → CofProp)
    (A : Γ → Type ℓ)
    (β : FibStr (A ∘ wk[ φ ]))
    (α : FibStr A)
    → FibStr A
  realignFibStr φ A β α .lift S r p =
    RealignLift.filler (φ ∘ p) (β ∘ᶠˢ p ×id) (α ∘ᶠˢ p)
  realignFibStr φ A β α .vary S T σ r p =
    RealignVary.eq σ (φ ∘ p) (β ∘ᶠˢ p ×id) (α ∘ᶠˢ p)

  -- TODO prove this in RealignLift?
  isRealigned : (φ : Γ → CofProp)
    {A : Γ → Type ℓ}
    (β : FibStr (A ∘ wk[ φ ]))
    (α : FibStr A)
    → realignFibStr φ A β α ∘ᶠˢ fst ≡ β
  isRealigned φ β α =
    FibStrExt λ S r p box s →
      sym $
      RealignLift.fillA _
        (β ∘ᶠˢ ((wk[ φ ] ∘ p) ×id))
        (α ∘ᶠˢ (wk[ φ ] ∘ p)) _
        .fill s .out≡ (∨r (snd ∘ p))

  reindexRealignFibStr : (φ : Γ → CofProp)
    {A : Γ → Type ℓ}
    (β : FibStr (A ∘ wk[ φ ]))
    (α : FibStr A)
    (ρ : Δ → Γ)
    → realignFibStr φ A β α ∘ᶠˢ ρ
    ≡ realignFibStr (φ ∘ ρ) (A ∘ ρ) (β ∘ᶠˢ ρ ×id) (α ∘ᶠˢ ρ)
  reindexRealignFibStr φ β α ρ = FibStrExt λ S r p box s → refl

------------------------------------------------------------------------------------------
-- Realigning a fibration
------------------------------------------------------------------------------------------

opaque
  Realignᶠ : (φ : Γ → CofProp)
    (B : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    → Γ ⊢ᶠType ℓ
  Realignᶠ φ _ _ iso .fst γ = realign (φ γ) _ _ (iso ∘ (γ ,_))
  Realignᶠ φ (_ , β) (_ , α) iso .snd =
    realignFibStr φ _
      (subst FibStr (funext (uncurry λ γ → restrictsToA (φ γ) _ _ (iso ∘ (γ ,_)))) β)
      (isomorphFibStr (λ γ → isoB (φ γ) _ _ (iso ∘ (γ ,_))) α)

  isRealignedFib : (φ : Γ → CofProp)
    (B : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    → B ≡ Realignᶠ φ B A iso ∘ᶠ fst
  isRealignedFib φ (_ , β) (_ , α) iso =
    Σext _ (sym (isRealigned φ _ _))

  RealignᶠIso : (φ : Γ → CofProp)
    (B : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    → Γ ⊢ Realignᶠ φ B A iso .fst ≅ᴵ A .fst
  RealignᶠIso φ B A iso γ = isoB _ _ _ _

  reindexRealignᶠ : (φ : Γ → CofProp)
    (B : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    (ρ : Δ → Γ)
    → Realignᶠ φ B A iso ∘ᶠ ρ ≡ Realignᶠ (φ ∘ ρ) (B ∘ᶠ ρ ×id) (A ∘ᶠ ρ) (iso ∘ ρ ×id)
  reindexRealignᶠ φ (_ , β) (_ , α) iso ρ =
    Σext refl
      (reindexRealignFibStr _ _ _ ρ
        ∙ cong₂ (realignFibStr (φ ∘ ρ) _)
            (reindexSubst (ρ ×id) _ _ β)
            (reindexIsomorphFibStr (λ _ → isoB _ _ _ _) _ ρ))
