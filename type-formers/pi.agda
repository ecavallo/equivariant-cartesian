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
  (r : ⟨ S ⟩) (box : OpenBox S r (Π' A B))
  where

  module _ (s : ⟨ S ⟩) (a : A s) where

    boxA : OpenBox S s A
    boxA .cof = ⊥
    boxA .tube e _ = ∅-rec e
    boxA .cap .fst = a
    boxA .cap .snd ()

    fillA = α .lift S s id boxA

    module _ (cA : (i : ⟨ S ⟩) → A i) where

      q : ⟨ S ⟩ → Σ ⟨ S ⟩ A
      q i = (i , cA i)

      boxB : OpenBox S r (B ∘ q)
      boxB .cof = box .cof
      boxB .tube u i = box .tube u i (cA i)
      boxB .cap .fst = box .cap .fst (cA r)
      boxB .cap .snd u = appCong (box .cap .snd u)

      fillB = β .lift S r q boxB

abstract
  ΠIsFib :
    ∀{ℓ ℓ' ℓ''}{Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    {B : (Σ x ∈ Γ , A x) → Set ℓ''}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Π' A B)
  ΠIsFib {Γ = Γ} {A} {B} α β .lift S r p box =
    record
    { fill = λ s →
      ( (λ a →
          subst (curry B (p s))
            (fillA s a .cap≡)
            (fillB s a (fst ∘ fillA s a .fill) .fill s .fst))
      , λ u → funext λ a →
        symm (congdep (box .tube u s) (fillA s a .cap≡))
        ∙ cong (subst (curry B (p s)) (fillA s a .cap≡))
            (fillB s a (fst ∘ fillA s a .fill) .fill s .snd u)
      )
    ; cap≡ =
      funext λ a →
      cong (subst (curry B (p r)) (fillA r a .cap≡))
        (fillB r a (fst ∘ fillA r a .fill) .cap≡)
      ∙ congdep (box .cap .fst) (fillA r a .cap≡)
    }
    where
    open ΠIsFibId S (reindex A α p) (reindex B β (p ×id)) r box

  ΠIsFib {Γ = Γ} {A} {B} α β .vary S T σ r p box s =
    funext λ a →
    cong
      (subst (curry B (p (⟪ σ ⟫ s))) (T.fillA _ a .cap≡))
      (β .vary S T σ r (p ×id ∘ T.q _ a (fst ∘ T.fillA _ a .fill)) (T.boxB _ a (fst ∘ T.fillA _ a .fill)) s)
    ∙
    adjustSubstEq (curry B (p (⟪ σ ⟫ s)))
      (cong (λ cA → S.q s a cA s .snd) (funext (varyA a))) refl
      (T.fillA (⟪ σ ⟫ s) a .cap≡) (S.fillA s a .cap≡)
      (symm (substCongAssoc (curry B (p (⟪ σ ⟫ s))) (λ cA → S.q s a cA s .snd) (funext (varyA a)) _)
        ∙ congdep (λ cA → S.fillB s a cA .fill s .fst) (funext (varyA a)))
    where
    module T = ΠIsFibId T (reindex A α p) (reindex B β (p ×id)) (⟪ σ ⟫ r) box
    module S = ΠIsFibId S (reindex A α (p ∘ ⟪ σ ⟫)) (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) r (reshapeBox σ box)

    varyBoxA : ∀ a → reshapeBox σ (T.boxA (⟪ σ ⟫ s) a) ≡ S.boxA s a
    varyBoxA a = boxExt refl (λ ()) refl

    varyA : (a : A (p (⟪ σ ⟫ s))) (i : ⟨ S ⟩) → T.fillA _ a .fill _ .fst ≡ S.fillA s a .fill i .fst
    varyA a i =
      α .vary S T σ s p (T.boxA _ a) i
      ∙ cong (λ box → α .lift S s (p ∘ ⟪ σ ⟫) box .fill i .fst) (varyBoxA a)

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
  reindexΠ A B α β ρ = isFibExt λ _ _ _ _ _ → refl

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
