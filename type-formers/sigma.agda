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
  (r : ⟨ S ⟩) (box : OpenBox S r (Σ' A B))
  where

  boxA : OpenBox S r A
  boxA = mapBox (λ _ → fst) box

  fillA = α .lift S r id boxA

  module _ (cA : Filler boxA) where

    q : ⟨ S ⟩ → Σ ⟨ S ⟩ A
    q s = (s , cA .fill s .out)

    boxB : OpenBox S r (B ∘ q)
    boxB .cof = box .cof
    boxB .tube u i = subst (curry B i) (cA .fill i .out≡ u) (box .tube u i .snd)
    boxB .cap .out = subst (curry B r) (symm (cA .cap≡)) (box .cap .out .snd)
    boxB .cap .out≡ u =
      adjustSubstEq (curry B r)
        (cong fst (box .cap .out≡ u)) refl
        (cA .fill r .out≡ u) (symm (cA .cap≡))
        (symm (substCongAssoc (curry B r) fst (box .cap .out≡ u) _)
          ∙ congdep snd (box .cap .out≡ u))

    fillB = β .lift S r q boxB

opaque
  ΣIsFib : ∀ {ℓ ℓ' ℓ''}
    {Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    {B : (Σ x ∈ Γ , A x) → Set ℓ''}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Σ' A B)
  ΣIsFib {A = A} {B} α β .lift S r p box .fill s .out =
    (fillA .fill s .out , fillB fillA .fill s .out)
    where
    open ΣIsFibId S (reindex A α p) (reindex B β (p ×id)) r box

  ΣIsFib {A = A} {B} α β .lift S r p box .fill s .out≡ u =
    Σext (fillA .fill s .out≡ u) (fillB fillA .fill s .out≡ u)
    where
    open ΣIsFibId S (reindex A α p) (reindex B β (p ×id)) r box

  ΣIsFib {A = A} {B} α β .lift S r p box .cap≡ =
    Σext (fillA .cap≡)
      (adjustSubstEq (curry B (p r))
        refl (symm (fillA .cap≡))
        (fillA .cap≡) refl
        (fillB fillA .cap≡))
    where
    open ΣIsFibId S (reindex A α p) (reindex B β (p ×id)) r box

  ΣIsFib {A = A} {B} α β .vary S T σ r p box s =
    Σext
      (α .vary S T σ r p T.boxA s)
      (adjustSubstEq (curry B (p (⟪ σ ⟫ s)))
         refl refl
         (α .vary S T σ r p T.boxA s)
         (cong (λ cA → S.q cA s .snd) varyA)
         (β .vary S T σ r (p ×id ∘ T.q T.fillA) (T.boxB T.fillA) s)
       ∙ symm (substCongAssoc (curry B (p (⟪ σ ⟫ s))) (λ cA → S.q cA s .snd) varyA _)
       ∙ congdep (λ cA → S.fillB cA .fill s .out) varyA)
    where
    module T = ΣIsFibId T (reindex A α p) (reindex B β (p ×id)) (⟪ σ ⟫ r) box
    module S = ΣIsFibId S (reindex A α (p ∘ ⟪ σ ⟫)) (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) r (reshapeBox σ box)

    varyA : reshapeFiller σ T.fillA ≡ S.fillA
    varyA = fillerExt (α .vary S T σ r p T.boxA)

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
  reindexΣ A B α β ρ = isFibExt λ _ _ _ _ _ → refl

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
