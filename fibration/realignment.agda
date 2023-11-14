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

module RealignId {ℓ} {S : Shape}
  (Φ : ⟨ S ⟩ → CofProp)
  {A : ⟨ S ⟩ → Set ℓ}
  (β : isFib {Γ = ⟨ S ⟩ ,[ Φ ]} (A ∘ fst))
  (α : isFib A)
  {r : ⟨ S ⟩} (box : OpenBox S r A)
  where

  fillB : [ all S Φ ] → _
  fillB u = β .lift S r (λ s → s , u s) box

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

  fillA = α .lift S r id box' -- (ψ ∨ all S Φ) f' x₀'

opaque
  realignIsFib : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    (A : Γ → Set ℓ')
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    → ---------------
    isFib A
  realignIsFib Φ A β α .lift S r p box .fill s .out =
    fillA .fill s .out
    where
    open RealignId (Φ ∘ p) (reindex β (p ×id)) (reindex α p) box

  realignIsFib Φ A β α .lift S r p box .fill s .out≡ v =
    fillA .fill s .out≡ ∣ inl v ∣
    where
    open RealignId (Φ ∘ p) (reindex β (p ×id)) (reindex α p) box

  realignIsFib Φ A β α .lift S r p box .cap≡ =
    fillA .cap≡
    where
    open RealignId (Φ ∘ p) (reindex β (p ×id)) (reindex α p) box
  realignIsFib Φ A β α .vary S T σ r p box s =
    α .vary S T σ r p T.box' s
    ∙
    cong
      (λ box' → α .lift S r (p ∘ ⟪ σ ⟫) box' .fill s .out)
      (boxExt
        (cong (λ φ → box .cof ∨ φ) (allEquivariant σ (Φ ∘ p)))
        (takeOutCof (box .cof) (all T (Φ ∘ p)) (all S (Φ ∘ p ∘ ⟪ σ ⟫))
          (λ _ → refl)
          (λ uS uT → funext λ i →
            β .vary S T σ r (λ s → p s , uS s) box i
            ∙ cong (λ w → β .lift S r (λ s → p (⟪ σ ⟫ s) , w s) (reshapeBox σ box) .fill i .out)
              (funext λ s → cofIsProp (Φ (p (⟪ σ ⟫ s))) _ _)))
        refl)
    where
    module S =
      RealignId (Φ ∘ p ∘ ⟪ σ ⟫)
        (reindex β ((p ∘ ⟪ σ ⟫) ×id)) (reindex α (p ∘ ⟪ σ ⟫)) (reshapeBox σ box)
    module T = RealignId (Φ ∘ p) (reindex β (p ×id)) (reindex α p) box

  isRealigned : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ → Set ℓ'}
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    → ---------------
    reindex (realignIsFib Φ A β α) fst ≡ β
  isRealigned Φ β α =
    isFibExt λ S r p box s →
      let
        open RealignId (Φ ∘ fst ∘ p) (reindex β ((fst ∘ p) ×id)) (reindex α (fst ∘ p)) box
      in
      sym (fillA .fill s .out≡ ∣ inr (λ s → p s .snd) ∣)

  reindexRealignIsFib : ∀{ℓ ℓ' ℓ''}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {A : Γ → Set ℓ''}
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    (ρ : Δ → Γ)
    → ---------------
    reindex (realignIsFib Φ A β α) ρ
    ≡ realignIsFib (Φ ∘ ρ) (A ∘ ρ) (reindex β (ρ ×id)) (reindex α ρ)
  reindexRealignIsFib Φ β α ρ = isFibExt λ S r p box s → refl
