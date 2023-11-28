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

module RealignLift {S r} (Φ : ⟨ S ⟩ → CofProp)
  {A : ⟨ S ⟩ → Type ℓ}
  (β : FibStr (A ∘ wk[ Φ ]))
  (α : FibStr A)
  (box : OpenBox S r A)
  where

  fillB : [ all S Φ ] → _
  fillB u = β .lift S r (id ,, u) box

  box' : OpenBox S r A
  box' .cof = box .cof ∨ all S Φ
  box' .tube =
    ∨-rec (box .cof) (all S Φ)
      (box .tube)
      (λ u i → fillB u .fill i .out)
      (λ v u → funext λ i → fillB u .fill i .out≡ v)
  box' .cap .out = box .cap .out
  box' .cap .out≡ =
    ∨-elimEq (box .cof) (all S Φ)
      (box .cap .out≡)
      (λ u → fillB u .cap≡)

  fillA = α .lift S r id box'

  filler : Filler box
  filler .fill s .out = fillA .fill s .out
  filler .fill s .out≡ v = fillA .fill s .out≡ (∨l v)
  filler .cap≡ = fillA .cap≡

module RealignVary {S T} (σ : ShapeHom S T) {r}
  (Φ : ⟨ T ⟩ → CofProp)
  {A : ⟨ T ⟩ → Type ℓ}
  (β : FibStr (A ∘ wk[ Φ ]))
  (α : FibStr A)
  (box : OpenBox T (⟪ σ ⟫ r) A)
  where

  module T = RealignLift Φ β α box
  module S =
    RealignLift (Φ ∘ ⟪ σ ⟫)
      (β ∘ᶠˢ ⟪ σ ⟫ ×id) (α ∘ᶠˢ ⟪ σ ⟫) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    α .vary S T σ r id T.box' s
    ∙
    cong
      (λ box' → α .lift S r ⟪ σ ⟫ box' .fill s .out)
      (boxExt
        (cong (λ φ → box .cof ∨ φ) (allEquivariant σ Φ))
        (takeOutCof (box .cof) (all T Φ) (all S (Φ ∘ ⟪ σ ⟫))
          (λ _ → refl)
          (λ uS uT → funext λ i →
            β .vary S T σ r (id ,, uS) box i
            ∙ cong (λ w → β .lift S r (⟪ σ ⟫ ,, w) (reshapeBox σ box) .fill i .out)
              (funext λ s → cofIsProp (Φ (⟪ σ ⟫ s)) _ _)))
        refl)

opaque
  realignFibStr : (Φ : Γ → CofProp)
    (A : Γ → Type ℓ)
    (β : FibStr (A ∘ wk[ Φ ]))
    (α : FibStr A)
    → FibStr A
  realignFibStr Φ A β α .lift S r p =
    RealignLift.filler (Φ ∘ p) (β ∘ᶠˢ p ×id) (α ∘ᶠˢ p)
  realignFibStr Φ A β α .vary S T σ r p =
    RealignVary.eq σ (Φ ∘ p) (β ∘ᶠˢ p ×id) (α ∘ᶠˢ p)

  -- TODO prove this in RealignLift?
  isRealigned : (Φ : Γ → CofProp)
    {A : Γ → Type ℓ}
    (β : FibStr (A ∘ wk[ Φ ]))
    (α : FibStr A)
    → realignFibStr Φ A β α ∘ᶠˢ fst ≡ β
  isRealigned Φ β α =
    FibStrExt λ S r p box s →
      sym $
      RealignLift.fillA _
        (β ∘ᶠˢ ((wk[ Φ ] ∘ p) ×id))
        (α ∘ᶠˢ (wk[ Φ ] ∘ p)) _
        .fill s .out≡ (∨r (snd ∘ p))

  reindexRealignFibStr : (Φ : Γ → CofProp)
    {A : Γ → Type ℓ}
    (β : FibStr (A ∘ wk[ Φ ]))
    (α : FibStr A)
    (ρ : Δ → Γ)
    → realignFibStr Φ A β α ∘ᶠˢ ρ
    ≡ realignFibStr (Φ ∘ ρ) (A ∘ ρ) (β ∘ᶠˢ ρ ×id) (α ∘ᶠˢ ρ)
  reindexRealignFibStr Φ β α ρ = FibStrExt λ S r p box s → refl

------------------------------------------------------------------------------------------
-- Realigning a fibration
------------------------------------------------------------------------------------------

opaque
  Realignᶠ : (Φ : Γ → CofProp)
    (B : Γ ,[ Φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ,[ Φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    → Γ ⊢ᶠType ℓ
  Realignᶠ Φ _ _ iso .fst γ = realign (Φ γ) _ _ (iso ∘ (γ ,_))
  Realignᶠ Φ (_ , β) (_ , α) iso .snd =
    realignFibStr Φ _
      (subst FibStr (funext (uncurry λ γ → restrictsToA (Φ γ) _ _ (iso ∘ (γ ,_)))) β)
      (isomorphFibStr (λ γ → isoB (Φ γ) _ _ (iso ∘ (γ ,_))) α)

  isRealignedFib : (Φ : Γ → CofProp)
    (B : Γ ,[ Φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ,[ Φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    → B ≡ Realignᶠ Φ B A iso ∘ᶠ fst
  isRealignedFib Φ (_ , β) (_ , α) iso =
    Σext _ (sym (isRealigned Φ _ _))

  RealignᶠIso : (Φ : Γ → CofProp)
    (B : Γ ,[ Φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ,[ Φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    → Γ ⊢ Realignᶠ Φ B A iso .fst ≅ᴵ A .fst
  RealignᶠIso Φ B A iso γ = isoB _ _ _ _

  reindexRealignᶠ : (Φ : Γ → CofProp)
    (B : Γ ,[ Φ ] ⊢ᶠType ℓ)
    (A : Γ ⊢ᶠType ℓ)
    (iso : Γ ,[ Φ ] ⊢ B .fst ≅ᴵ (A .fst ∘ fst))
    (ρ : Δ → Γ)
    → Realignᶠ Φ B A iso ∘ᶠ ρ ≡ Realignᶠ (Φ ∘ ρ) (B ∘ᶠ ρ ×id) (A ∘ᶠ ρ) (iso ∘ ρ ×id)
  reindexRealignᶠ Φ (_ , β) (_ , α) iso ρ =
    Σext refl
      (reindexRealignFibStr _ _ _ ρ
        ∙ cong₂ (realignFibStr (Φ ∘ ρ) _)
            (reindexSubst (ρ ×id) _ _ β)
            (reindexIsomorphFibStr (λ _ → isoB _ _ _ _) _ ρ))
