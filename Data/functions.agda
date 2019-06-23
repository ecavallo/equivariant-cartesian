{-

Fibrancy of Π-types.

-}
{-# OPTIONS --rewriting #-}
module Data.functions where

open import prelude
open import interval
open import cofprop
open import fibrations

----------------------------------------------------------------------
-- Dependent functions
----------------------------------------------------------------------
Π' : ∀{a}{Γ : Set a}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Π' A B x = (a : A x) → B (x , a)

module FibΠId
  (S : Shape) {A : ⟨ S ⟩ → Set} {B : Σ ⟨ S ⟩ A → Set}
  (α : isFib A) (β : isFib B)
  (r : ⟨ S ⟩) (φ : CofProp) (f : [ φ ] → (s : ⟨ S ⟩) → Π (curry B s))
  (x₀ : Π (curry B r) [ φ ↦ f ◆ r ])
  where

  module _ (s : ⟨ S ⟩) (a : A s) where

    tubeA : [ int ∋ O ≈ I ] → Π A
    tubeA O≡I _ = O≠I O≡I

    baseA : A s [ int ∋ O ≈ I ↦ tubeA ◆ s ]
    baseA = (a , λ O≡I → O≠I O≡I)

    compA = α .lift S s id (int ∋ O ≈ I) tubeA baseA

    module _ (cA : Comp S s A (int ∋ O ≈ I) tubeA baseA) where

      q : ⟨ S ⟩ → Σ ⟨ S ⟩ A
      q i = (i , cA .comp i .fst)

      tubeB : [ φ ] → Π (B ∘ q)
      tubeB u i = f u i (cA .comp i .fst)

      baseB : B (q r) [ φ ↦ tubeB ◆ r ]
      baseB =
        ( x₀ .fst (cA .comp r .fst)
        , λ u → appCong (x₀ .snd u)
        )

      compB = β .lift S r q φ tubeB baseB

abstract
  FibΠ :
    ∀{a}{Γ : Set a}
    {A : Γ → Set}
    {B : (Σ x ∈ Γ , A x) → Set}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Π' A B)
  FibΠ {_} {Γ} {A} {B} α β .lift S r p φ f x₀ =
    record
    { comp = λ s →
      ( (λ a →
          subst (curry B (p s))
            (compA s a .cap)
            (compB s a (compA s a) .comp s .fst))
      , λ u → funext λ a →
        trans
          (cong (subst (curry B (p s)) (compA s a .cap))
            (compB s a (compA s a) .comp s .snd u))
          (symm (congdep (f u s) (compA s a .cap)))
      )
    ; cap =
      funext λ a → 
      trans
        (congdep (x₀ .fst) (compA r a .cap))
        (cong (subst (curry B (p r)) (compA r a .cap))
          (compB r a (compA r a) .cap))
    }
    where
    open FibΠId S (reindex A α p) (reindex B β (p ×id)) r φ f x₀

  FibΠ {_} {Γ} {A} {B} α β .vary S T σ r p φ f x₀ s =
    funext λ a →
    trans
      (adjustSubstEq (curry B (p (⟪ σ ⟫ s)))
        (cong (λ cA → S.q s a cA s .snd) (varyA a)) refl
        (T.compA (⟪ σ ⟫ s) a .cap) (S.compA s a .cap)
        (trans
          (congdep (λ cA → S.compB s a cA .comp s .fst) (varyA a))
          (symm (subst-cong-assoc (curry B (p (⟪ σ ⟫ s))) (λ cA → S.q s a cA s .snd) (varyA a) _))))
      (cong
        (subst (curry B (p (⟪ σ ⟫ s))) (T.compA _ a .cap))
        (β .vary S T σ r (p ×id ∘ T.q _ a (T.compA _ a)) φ
          (T.tubeB _ a (T.compA _ a)) (T.baseB _ a (T.compA _ a))
          s))
    where
    module T = FibΠId T (reindex A α p) (reindex B β (p ×id)) (⟪ σ ⟫ r) φ f x₀
    module S = FibΠId S (reindex A α (p ∘ ⟪ σ ⟫)) (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) r φ (f ◇ ⟪ σ ⟫) x₀

    varyA : (a : A (p (⟪ σ ⟫ s))) → reshapeComp σ (T.compA _ a) ≡ S.compA _ a
    varyA a = compExt (α .vary S T σ s p (int ∋ O ≈ I) (T.tubeA _ a) (T.baseA _ a))

  FibΠ' :
    {Γ : Set}
    (A : Fib Γ)
    (B : Fib (Σ x ∈ Γ , fst A x))
    → -----------
    Fib Γ
  FibΠ' (A , α) (B , β) = (Π' A B , FibΠ {A = A} {B = B} α β)

  ----------------------------------------------------------------------
  -- Forming Π-types is stable under reindexing
  ----------------------------------------------------------------------
  reindexΠ : ∀ {ℓ ℓ'}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ → Set)
    (B : Σ Γ A → Set)
    (α : isFib A)
    (β : isFib B)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Π' A B) (FibΠ {B = B} α β) ρ ≡ FibΠ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
  reindexΠ A B α β ρ = fibExt λ _ _ _ _ _ _ _ → refl
