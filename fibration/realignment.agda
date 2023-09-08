{-

Realign a fibration structure to agree with another on some cofibration

-}
{-# OPTIONS --rewriting #-}
module fibration.realignment where

open import prelude
open import axioms
open import fibration.fibration

module RealignId {ℓ} (S : Shape)
  (Φ : ⟨ S ⟩ → CofProp)
  (A : ⟨ S ⟩ → Set ℓ)
  (β : isFib {Γ = ⟨ S ⟩ ,[ Φ ]} (A ∘ fst))
  (α : isFib A)
  (r : ⟨ S ⟩) (ψ : CofProp) (f : [ ψ ] → Π A)
  (x₀ : A r [ ψ ↦ f ◆ r ])
  where

  compB : [ all S Φ ] → _
  compB u = β .lift S r (λ s → s , u s) ψ f x₀

  f' : [ ψ ∨ all S Φ ] → Π A
  f' =
    ∨-rec ψ (all S Φ)
      f
      (λ u i → compB u .comp i .fst)
      (λ v u → funext λ i → compB u .comp i .snd v)

  x₀' : A r [ ψ ∨ all S Φ ↦ f' ◆ r ]
  x₀' =
    ( x₀ .fst
    , ∨-elimEq ψ (all S Φ)
      (x₀ .snd)
      (λ u → compB u .cap)
    )

  compA = α .lift S r id (ψ ∨ all S Φ) f' x₀'

abstract

  realignIsFib : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    (A : Γ → Set ℓ')
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    → ---------------
    isFib A
  realignIsFib Φ A β α .lift S r p ψ f x₀ =
    record
    { comp = λ s →
      ( compA .comp s .fst
      , λ v → compA .comp s .snd ∣ inl v ∣
      )
    ; cap = compA .cap
    }
    where
    open RealignId S (Φ ∘ p) (A ∘ p) (reindex (A ∘ fst) β (p ×id)) (reindex A α p) r ψ f x₀
  realignIsFib Φ A β α .vary S T σ r p ψ f x₀ s =
    trans
      (cong
        (λ {(φ , f , x₀) → α .lift S r (p ∘ ⟪ σ ⟫) φ f x₀ .comp s .fst})
        (boxEq S
          (cong (λ φ → ψ ∨ φ) (allEquivariant σ (Φ ∘ p)))
          (takeOutCof ψ (all T (Φ ∘ p)) (all S (Φ ∘ p ∘ ⟪ σ ⟫))
            (λ _ → refl)
            (λ uS uT → funext λ i →
              trans
                (cong
                  (λ w → β .lift S r (λ s → p (⟪ σ ⟫ s) , w s) ψ (f ◇ ⟪ σ ⟫) x₀ .comp i .fst)
                  (funext λ s → cofIsProp (Φ (p (⟪ σ ⟫ s))) _ _))
                (β .vary S T σ r (λ s → p s , uS s) ψ f x₀ i)))
          r
          refl))
      (α .vary S T σ r p (ψ ∨ all T (Φ ∘ p)) T.f' T.x₀' s)
    where
    module S =
      RealignId S (Φ ∘ p ∘ ⟪ σ ⟫) (A ∘ p ∘ ⟪ σ ⟫)
        (reindex (A ∘ fst) β ((p ∘ ⟪ σ ⟫) ×id)) (reindex A α (p ∘ ⟪ σ ⟫)) r ψ (f ◇ ⟪ σ ⟫) x₀
    module T =
      RealignId T (Φ ∘ p) (A ∘ p)
        (reindex (A ∘ fst) β (p ×id)) (reindex A α p) (⟪ σ ⟫ r) ψ f x₀

  isRealigned : ∀ {ℓ ℓ'}
    {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    (A : Γ → Set ℓ')
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    → ---------------
    reindex A (realignIsFib Φ A β α) fst ≡ β
  isRealigned {ℓ} {Γ} Φ A β α =
    isFibExt λ S r p ψ f x₀ s →
      let
        open RealignId S (Φ ∘ fst ∘ p) (A ∘ fst ∘ p)
          (reindex (A ∘ fst) β ((fst ∘ p) ×id)) (reindex A α (fst ∘ p)) r ψ f x₀
      in
      symm (compA .comp s .snd ∣ inr (λ s → p s .snd) ∣)

  reindexRealignIsFib : ∀{ℓ ℓ' ℓ''}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    (A : Γ → Set ℓ'')
    (β : isFib {Γ = Γ ,[ Φ ]} (A ∘ fst))
    (α : isFib A)
    (ρ : Δ → Γ)
    → ---------------
    reindex A (realignIsFib Φ A β α) ρ
    ≡ realignIsFib (Φ ∘ ρ) (A ∘ ρ) (reindex (A ∘ fst) β (ρ ×id)) (reindex A α ρ)
  reindexRealignIsFib Φ A β α ρ = isFibExt λ S r p ψ f x₀ s → refl