{-

Fibrancy of Path types.

-}
{-# OPTIONS --rewriting #-}
module Data.paths where

open import prelude
open import shape
open import cofprop
open import fibrations

----------------------------------------------------------------------
-- Path types
----------------------------------------------------------------------

Path' : ∀{ℓ ℓ'}{Γ : Set ℓ}(A : Γ → Set ℓ') → Σ x ∈ Γ , A x × A x → Set ℓ'
Path' A (x , (a , a')) = a ~ a'

module FibPathId {ℓ}
  (S : Shape) {A : ⟨ S ⟩ → Set ℓ} {a₀ : Π A} {a₁ : Π A}
  (α : isFib A)
  (r : ⟨ S ⟩) (φ : CofProp) (f : [ φ ] → (s : ⟨ S ⟩) → a₀ s ~ a₁ s)
  (x₀ : (a₀ r ~ a₁ r) [ φ ↦ f ◆ r ])
  where

  module _ (i : Int) where

    tubeA : [ φ ∨ ∂ i ] → (s : ⟨ S ⟩) → A s
    tubeA =
      ∨-rec φ (∂ i)
        (λ u s → f u s .at i)
        (OI-rec i
          (λ {refl → a₀})
          (λ {refl → a₁}))
        (λ u → OI-elim i
          (λ {refl → funext λ s → f u s .atO})
          (λ {refl → funext λ s → f u s .atI}))

    baseA : A r [ φ ∨ ∂ i ↦ tubeA ◆ r ]
    baseA =
      ( x₀ .fst .at i
      , ∨-elimEq φ (∂ i)
        (λ u → cong (λ q → q .at i) (x₀ .snd u))
        (OI-elim i
          (λ {refl → symm (x₀ .fst .atO)})
          (λ {refl → symm (x₀ .fst .atI)}))
      )

    compA = α .lift S r id (φ ∨ ∂ i) tubeA baseA

abstract
  FibPath :
    ∀{ℓ ℓ'} {Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    (α : isFib A)
    → -----------
    isFib (Path' A)
  FibPath {A = A} α .lift S r p φ f x₀ =
    record
    { comp = λ s →
      ( path
        (λ i → compA i .comp s .fst)
        (symm (compA O .comp s .snd ∣ inr ∣ inl refl ∣ ∣))
        (symm (compA I .comp s .snd ∣ inr ∣ inr refl ∣ ∣))
      , λ u → PathExt λ i → compA i .comp s .snd ∣ inl u ∣
      )
    ; cap = PathExt λ i → compA i .cap
    }
    where
    open FibPathId S (reindex A α (fst ∘ p)) r φ f x₀

  FibPath {A = A} α .vary S T σ r p φ f x₀ s =
    PathExt λ i →
    trans
      (cong
        (λ {(t , m) → α .lift S r (fst ∘ p ∘ ⟪ σ ⟫) (φ ∨ ∂ i) t (T.baseA i .fst , m) .comp s .fst})
        (Σext
          (funext
            (∨-elimEq φ (∂ i)
              (λ u → refl)
              (OI-elim i
                (λ {refl → refl})
                (λ {refl → refl}))))
          (funext λ _ → uipImp)))
      (α .vary S T σ r (fst ∘ p) (φ ∨ ∂ i) (T.tubeA i) (T.baseA i) s)
    where
    module T = FibPathId T (reindex A α (fst ∘ p)) (⟪ σ ⟫ r) φ f x₀
    module S = FibPathId S (reindex A α (fst ∘ p ∘ ⟪ σ ⟫)) r φ (f ◇ ⟪ σ ⟫) x₀

  ----------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------
  reindexPath :
    ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ → Set ℓ'')
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Path' A) (FibPath α) (ρ ×id) ≡ FibPath (reindex A α ρ)
  reindexPath A α ρ = fibExt λ _ _ _ _ _ _ _ → refl
