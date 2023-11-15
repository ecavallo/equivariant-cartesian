{-

Realign a fibration structure to agree with another on some cofibration

TODO: package with Set-realignment to get a proof that fibrations (not just their structures) can be
realigned

-}
{-# OPTIONS --rewriting #-}
module fibration.realignment where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ ℓ' ℓ'' : Level

module RealignLift {S r}
  (Φ : ⟨ S ⟩ → CofProp)
  {A : ⟨ S ⟩ → Set ℓ}
  (β : isFib {Γ = ⟨ S ⟩ ,[ Φ ]} (A ∘ fst))
  (α : isFib A)
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
  filler .fill s .out≡ v = fillA .fill s .out≡ ∣ inl v ∣
  filler .cap≡ = fillA .cap≡

module RealignVary {S T} (σ : ShapeHom S T) {r}
  (Φ : ⟨ T ⟩ → CofProp)
  {A : ⟨ T ⟩ → Set ℓ}
  (β : isFib {Γ = ⟨ T ⟩ ,[ Φ ]} (A ∘ fst))
  (α : isFib A)
  (box : OpenBox T (⟪ σ ⟫ r) A)
  where

  module T = RealignLift Φ β α box
  module S =
    RealignLift (Φ ∘ ⟪ σ ⟫)
      (reindex β (⟪ σ ⟫ ×id)) (reindex α ⟪ σ ⟫) (reshapeBox σ box)

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
  realignIsFib : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    (A : Γ → Set ℓ')
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    → ---------------
    isFib A
  realignIsFib Φ A β α .lift S r p =
    RealignLift.filler (Φ ∘ p) (reindex β (p ×id)) (reindex α p)
  realignIsFib Φ A β α .vary S T σ r p =
    RealignVary.eq σ (Φ ∘ p) (reindex β (p ×id)) (reindex α p)

  isRealigned : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ → Set ℓ'}
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    → ---------------
    reindex (realignIsFib Φ A β α) fst ≡ β
  isRealigned Φ β α =
    isFibExt λ S r p box s →
      let
        open RealignLift (Φ ∘ fst ∘ p) (reindex β ((fst ∘ p) ×id)) (reindex α (fst ∘ p)) box
      in
      sym (fillA .fill s .out≡ ∣ inr (λ s → p s .snd) ∣)

  reindexRealignIsFib : {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {A : Γ → Set ℓ''}
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    (ρ : Δ → Γ)
    → ---------------
    reindex (realignIsFib Φ A β α) ρ
    ≡ realignIsFib (Φ ∘ ρ) (A ∘ ρ) (reindex β (ρ ×id)) (reindex α ρ)
  reindexRealignIsFib Φ β α ρ = isFibExt λ S r p box s → refl
