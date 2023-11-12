{-

Fibration structure on Σ-types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.sigma where

open import prelude
open import axioms
open import fibration.fibration

Σ' : ∀{ℓ ℓ' ℓ''} {Γ : Set ℓ} (A : Γ → Set ℓ') (B : Σ Γ A → Set ℓ'')
  → Γ → Set (ℓ' ⊔ ℓ'')
Σ' A B x = Σ a ∈ A x , B (x , a)

_×'_ : ∀{ℓ ℓ' ℓ''} {Γ : Set ℓ} (A : Γ → Set ℓ') (B : Γ → Set ℓ'')
  → Γ → Set (ℓ' ⊔ ℓ'')
(A ×' B) x = A x × B x


module ΣIsFibId {ℓ ℓ'}
  (S : Shape) {A : ⟨ S ⟩ → Set ℓ} {B : Σ ⟨ S ⟩ A → Set ℓ'}
  (α : isFib A) (β : isFib B)
  (r : ⟨ S ⟩) (φ : CofProp) (f : [ φ ] → (s : ⟨ S ⟩) → Σ (A s) (curry B s))
  (x₀ : Σ (A r) (curry B r) [ φ ↦ f ◆ r ])
  where

  tubeA : [ φ ] → Π A
  tubeA u i = f u i .fst

  baseA : A r [ φ ↦ tubeA ◆ r ]
  baseA = (x₀ .fst .fst , λ u → cong fst (x₀ .snd u))

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
          (symm (substCongAssoc (curry B r) fst (x₀ .snd u) _)
            ∙ congdep snd (x₀ .snd u))
      )

    compB = β .lift S r q φ tubeB baseB

abstract
  ΣIsFib : ∀ {ℓ ℓ' ℓ''}
    {Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    {B : (Σ x ∈ Γ , A x) → Set ℓ''}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Σ' A B)
  ΣIsFib {Γ = Γ} {A} {B} α β .lift S r p φ f x₀ =
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
    open ΣIsFibId S (reindex A α p) (reindex B β (p ×id)) r φ f x₀

  ΣIsFib {Γ = Γ} {A} {B} α β .vary S T σ r p φ f x₀ s =
    Σext
      (α .vary S T σ r p φ T.tubeA T.baseA s)
      (adjustSubstEq (curry B (p (⟪ σ ⟫ s)))
         refl refl
         (α .vary S T σ r p φ T.tubeA T.baseA s)
         (cong (λ cA → S.q cA s .snd) varyA)
         (β .vary S T σ r (p ×id ∘ T.q T.compA) φ (T.tubeB T.compA) (T.baseB T.compA) s)
       ∙ symm (substCongAssoc (curry B (p (⟪ σ ⟫ s))) (λ cA → S.q cA s .snd) varyA _)
       ∙ congdep (λ cA → S.compB cA .comp s .fst) varyA)
    where
    module T = ΣIsFibId T (reindex A α p) (reindex B β (p ×id)) (⟪ σ ⟫ r) φ f x₀
    module S = ΣIsFibId S (reindex A α (p ∘ ⟪ σ ⟫)) (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) r φ (f ◇ ⟪ σ ⟫) x₀

    varyA : reshapeComp σ T.compA ≡ S.compA
    varyA = compExt (α .vary S T σ r p φ T.tubeA T.baseA)

  ----------------------------------------------------------------------
  -- Forming Σ-types is stable under reindexing
  ----------------------------------------------------------------------
  reindexΣ : ∀ {ℓ ℓ' ℓ'' ℓ'''}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ → Set ℓ'')
    (B : Σ Γ A → Set ℓ''')
    (α : isFib A)
    (β : isFib B)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Σ' A B) (ΣIsFib α β) ρ ≡ ΣIsFib (reindex A α ρ) (reindex B β (ρ ×id))
  reindexΣ A B α β ρ = isFibExt λ _ _ _ _ _ _ _ → refl

FibΣ : ∀ {ℓ ℓ' ℓ''}
  {Γ : Set ℓ}
  (A : Fib ℓ' Γ)
  (B : Fib ℓ'' (Σ x ∈ Γ , fst A x))
  → -----------
  Fib (ℓ' ⊔ ℓ'') Γ
FibΣ (A , α) (B , β) = Σ' A B , ΣIsFib α β

reindexFibΣ : ∀ {ℓ ℓ' ℓ'' ℓ'''}
  {Δ : Set ℓ} {Γ : Set ℓ'}
  (Aα : Fib ℓ'' Γ)
  (Bβ : Fib ℓ''' (Σ Γ (Aα .fst)))
  (ρ : Δ → Γ)
  → ----------------------
  reindexFib (FibΣ Aα Bβ) ρ ≡ FibΣ (reindexFib Aα ρ) (reindexFib Bβ (ρ ×id))
reindexFibΣ (A , α) (B , β) ρ = Σext refl (reindexΣ A B α β ρ)
