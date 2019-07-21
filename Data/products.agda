{-

Fibrancy of Σ-types.

-}
{-# OPTIONS --rewriting #-}
module Data.products where

open import prelude
open import shape
open import cofprop
open import fibrations

----------------------------------------------------------------------
-- Dependent products
----------------------------------------------------------------------

Σ' : ∀{a}{Γ : Set a}(A : Γ → Set)(B : Σ Γ A → Set) → Γ → Set
Σ' A B x = Σ a ∈ A x , B (x , a)

_×'_ : ∀{a}{Γ : Set a}(A : Γ → Set)(B : Γ → Set) → Γ → Set
(A ×' B) x = A x × B x


module FibΣId
  (S : Shape) {A : ⟨ S ⟩ → Set} {B : Σ ⟨ S ⟩ A → Set}
  (α : isFib A) (β : isFib B)
  (r : ⟨ S ⟩) (φ : CofProp) (f : [ φ ] → (s : ⟨ S ⟩) → Σ (A s) (curry B s))
  (x₀ : Σ (A r) (curry B r) [ φ ↦ f ◆ r ])
  where

  tubeA : [ φ ] → Π A
  tubeA u i = f u i .fst

  baseA : A r [ φ ↦ tubeA ◆ r ]
  baseA = (x₀ .fst .fst , λ u → Σeq₁ (x₀ .snd u))

  compA = α .lift S r id φ tubeA baseA

  module _ (cA : Comp S r A φ tubeA baseA) where

    q : ⟨ S ⟩ → Σ ⟨ S ⟩ A
    q s = (s , cA .comp s .fst)

    tubeB : [ φ ] → Π (B ∘ q)
    tubeB u i =
      subst (curry B i) (cA .comp i .snd u) (f u i .snd)

    baseB : B (q r) [ φ ↦ tubeB ◆ r ]
    baseB =
      ( subst (curry B r) (symm (cA .cap)) (x₀ .fst .snd)
      , λ u →
        adjustSubstEq (curry B r)
          (cong fst (x₀ .snd u)) refl
          (cA .comp r .snd u) (symm (cA .cap))
          (trans
            (congdep snd (x₀ .snd u))
            (symm (substCongAssoc (curry B r) fst (x₀ .snd u) _)))
      )

    compB = β .lift S r q φ tubeB baseB

abstract
  FibΣ : ∀ {ℓ}
    {Γ : Set ℓ}
    {A : Γ → Set}
    {B : (Σ x ∈ Γ , A x) → Set}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Σ' A B)
  FibΣ {Γ = Γ} {A} {B} α β .lift S r p φ f x₀ =
    record
    { comp = λ s →
      ( (compA .comp s .fst , compB compA .comp s .fst)
      , λ u → Σext (compA .comp s .snd u) (compB compA .comp s .snd u)
      )
    ; cap =
      Σext (compA .cap)
        (adjustSubstEq (curry B (p r))
          refl (symm (compA .cap))
          (compA .cap) refl
          (compB compA .cap))
    }
    where
    open FibΣId S (reindex A α p) (reindex B β (p ×id)) r φ f x₀

  FibΣ {Γ = Γ} {A} {B} α β .vary S T σ r p φ f x₀ s =
    Σext
      (α .vary S T σ r p φ T.tubeA T.baseA s)
      (trans
        (trans
          (congdep (λ cA → S.compB cA .comp s .fst) varyA)
          (symm (substCongAssoc (curry B (p (⟪ σ ⟫ s))) (λ cA → S.q cA s .snd) varyA _)))
        (adjustSubstEq (curry B (p (⟪ σ ⟫ s)))
          refl refl
          (α .vary S T σ r p φ T.tubeA T.baseA s)
          (cong (λ cA → S.q cA s .snd) varyA)
          (β .vary S T σ r (p ×id ∘ T.q T.compA) φ (T.tubeB T.compA) (T.baseB T.compA) s)))
    where
    module T = FibΣId T (reindex A α p) (reindex B β (p ×id)) (⟪ σ ⟫ r) φ f x₀
    module S = FibΣId S (reindex A α (p ∘ ⟪ σ ⟫)) (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) r φ (f ◇ ⟪ σ ⟫) x₀

    varyA : reshapeComp σ T.compA ≡ S.compA
    varyA = compExt (α .vary S T σ r p φ T.tubeA T.baseA)

  ----------------------------------------------------------------------
  -- Forming Σ-types is stable under reindexing
  ----------------------------------------------------------------------
  reindexΣ : ∀ {ℓ ℓ'}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ → Set)
    (B : Σ Γ A → Set)
    (α : isFib A)
    (β : isFib B)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Σ' A B) (FibΣ {B = B} α β) ρ ≡ FibΣ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
  reindexΣ A B α β ρ = fibExt λ _ _ _ _ _ _ _ → refl

FibΣ' : ∀ {ℓ}
  {Γ : Set ℓ}
   (A : Fib Γ)
  (B : Fib (Σ x ∈ Γ , fst A x))
  → -----------
  Fib Γ
FibΣ' (A , α) (B , β) = Σ' A B , FibΣ {A = A} {B = B} α β

reindexΣ' : ∀ {ℓ ℓ'}
  {Δ : Set ℓ} {Γ : Set ℓ'}
  (Aα : Fib Γ)
  (Bβ : Fib (Σ Γ (Aα .fst)))
  (ρ : Δ → Γ)
  → ----------------------
  reindex' (FibΣ' Aα Bβ) ρ ≡ FibΣ' (reindex' Aα ρ) (reindex' Bβ (ρ ×id))
reindexΣ' (A , α) (B , β) ρ = Σext refl (reindexΣ A B α β ρ)
