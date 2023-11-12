{-

Fibration structure on Π-types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.pi where

open import prelude
open import axioms
open import fibration.fibration

Π' : ∀{ℓ ℓ' ℓ''} {Γ : Set ℓ}(A : Γ → Set ℓ')(B : (Σ x ∈ Γ , A x) → Set ℓ'')
  → Γ → Set (ℓ' ⊔ ℓ'')
Π' A B x = (a : A x) → B (x , a)

module ΠIsFibId {ℓ ℓ'}
  (S : Shape) {A : ⟨ S ⟩ → Set ℓ} {B : Σ ⟨ S ⟩ A → Set ℓ'}
  (α : isFib A) (β : isFib B)
  (r : ⟨ S ⟩) (φ : CofProp) (f : [ φ ] → (s : ⟨ S ⟩) → Π (curry B s))
  (x₀ : Π (curry B r) [ φ ↦ f ◆ r ])
  where

  module _ (s : ⟨ S ⟩) (a : A s) where

    tubeA : [ ⊥ ] → Π A
    tubeA e _ = ∅-rec e

    baseA : A s [ ⊥ ↦ tubeA ◆ s ]
    baseA = (a , λ ())

    compA = α .lift S s id ⊥ tubeA baseA

    module _ (cA : Comp S s A ⊥ tubeA baseA) where

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
  ΠIsFib :
    ∀{ℓ ℓ' ℓ''}{Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    {B : (Σ x ∈ Γ , A x) → Set ℓ''}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Π' A B)
  ΠIsFib {Γ = Γ} {A} {B} α β .lift S r p φ f x₀ =
    record
    { comp = λ s →
      ( (λ a →
          subst (curry B (p s))
            (compA s a .cap)
            (compB s a (compA s a) .comp s .fst))
      , λ u → funext λ a →
        symm (congdep (f u s) (compA s a .cap))
        ∙ cong (subst (curry B (p s)) (compA s a .cap))
            (compB s a (compA s a) .comp s .snd u)
      )
    ; cap =
      funext λ a →
      cong (subst (curry B (p r)) (compA r a .cap))
        (compB r a (compA r a) .cap)
      ∙ congdep (x₀ .fst) (compA r a .cap)
    }
    where
    open ΠIsFibId S (reindex A α p) (reindex B β (p ×id)) r φ f x₀

  ΠIsFib {Γ = Γ} {A} {B} α β .vary S T σ r p φ f x₀ s =
    funext λ a →
    cong
      (subst (curry B (p (⟪ σ ⟫ s))) (T.compA _ a .cap))
      (β .vary S T σ r (p ×id ∘ T.q _ a (T.compA _ a)) φ
        (T.tubeB _ a (T.compA _ a)) (T.baseB _ a (T.compA _ a))
        s)
    ∙
    adjustSubstEq (curry B (p (⟪ σ ⟫ s)))
      (cong (λ cA → S.q s a cA s .snd) (varyA a)) refl
      (T.compA (⟪ σ ⟫ s) a .cap) (S.compA s a .cap)
      (symm (substCongAssoc (curry B (p (⟪ σ ⟫ s))) (λ cA → S.q s a cA s .snd) (varyA a) _)
        ∙ congdep (λ cA → S.compB s a cA .comp s .fst) (varyA a))
    where
    module T = ΠIsFibId T (reindex A α p) (reindex B β (p ×id)) (⟪ σ ⟫ r) φ f x₀
    module S = ΠIsFibId S (reindex A α (p ∘ ⟪ σ ⟫)) (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) r φ (f ◇ ⟪ σ ⟫) x₀

    varyA : (a : A (p (⟪ σ ⟫ s))) → reshapeComp σ (T.compA _ a) ≡ S.compA _ a
    varyA a = compExt (α .vary S T σ s p ⊥ (T.tubeA _ a) (T.baseA _ a))

  ----------------------------------------------------------------------
  -- Forming Π-types is stable under reindexing
  ----------------------------------------------------------------------
  reindexΠ : ∀ {ℓ ℓ' ℓ'' ℓ'''}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ → Set ℓ'')
    (B : Σ Γ A → Set ℓ''')
    (α : isFib A)
    (β : isFib B)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Π' A B) (ΠIsFib α β) ρ ≡ ΠIsFib (reindex A α ρ) (reindex B β (ρ ×id))
  reindexΠ A B α β ρ = isFibExt λ _ _ _ _ _ _ _ → refl

FibΠ : ∀ {ℓ ℓ' ℓ''}
  {Γ : Set ℓ}
  (A : Fib ℓ' Γ)
  (B : Fib ℓ'' (Σ x ∈ Γ , fst A x))
  → -----------
  Fib (ℓ' ⊔ ℓ'') Γ
FibΠ (A , α) (B , β) = (Π' A B , ΠIsFib α β)

reindexFibΠ : ∀ {ℓ ℓ' ℓ'' ℓ'''}
  {Δ : Set ℓ} {Γ : Set ℓ'}
  (Aα : Fib ℓ'' Γ)
  (Bβ : Fib ℓ''' (Σ Γ (Aα .fst)))
  (ρ : Δ → Γ)
  → ----------------------
  reindexFib (FibΠ Aα Bβ) ρ ≡ FibΠ (reindexFib Aα ρ) (reindexFib Bβ (ρ ×id))
reindexFibΠ (A , α) (B , β) ρ = Σext refl (reindexΠ A B α β ρ)
