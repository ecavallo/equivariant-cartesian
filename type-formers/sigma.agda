{-

Fibration structure on Σ-types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.sigma where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ ℓ' ℓ'' ℓ''' : Level

Σᴵ : {Γ : Type ℓ} (A : Γ → Type ℓ') (B : Σ Γ A → Type ℓ'')
  → Γ → Type (ℓ' ⊔ ℓ'')
Σᴵ A B x = Σ a ∈ A x , B (x , a)

_×ᴵ_ : {Γ : Type ℓ} (A : Γ → Type ℓ') (B : Γ → Type ℓ'')
  → Γ → Type (ℓ' ⊔ ℓ'')
(A ×ᴵ B) x = A x × B x

module ΣLift {S r}
  {A : ⟨ S ⟩ → Type ℓ} {B : Σ ⟨ S ⟩ A → Type ℓ'}
  (α : isFib A) (β : isFib B)
  (box : OpenBox S r (Σᴵ A B))
  where

  boxA : OpenBox S r A
  boxA = mapBox (λ _ → fst) box

  fillA = α .lift S r id boxA

  module _ (cA : Filler boxA) where

    boxB : OpenBox S r (B ∘ (id ,, out ∘ cA .fill))
    boxB .cof = box .cof
    boxB .tube u i = subst (curry B i) (cA .fill i .out≡ u) (box .tube u i .snd)
    boxB .cap .out = subst (curry B r) (sym (cA .cap≡)) (box .cap .out .snd)
    boxB .cap .out≡ u =
      adjustSubstEq (curry B r)
        (cong fst (box .cap .out≡ u)) refl
        (cA .fill r .out≡ u) (sym (cA .cap≡))
        (sym (substCongAssoc (curry B r) fst (box .cap .out≡ u) _)
          ∙ congdep snd (box .cap .out≡ u))

    fillB = β .lift S r (id ,, out ∘ cA .fill) boxB

  filler : Filler box
  filler .fill s .out .fst = fillA .fill s .out
  filler .fill s .out .snd = fillB fillA .fill s .out
  filler .fill s .out≡ u =
    Σext (fillA .fill s .out≡ u) (fillB fillA .fill s .out≡ u)
  filler .cap≡ =
    Σext (fillA .cap≡)
      (adjustSubstEq (curry B r)
        refl (sym (fillA .cap≡))
        (fillA .cap≡) refl
        (fillB fillA .cap≡))

module ΣVary {S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ → Type ℓ} {B : Σ ⟨ T ⟩ A → Type ℓ'}
  (α : isFib A) (β : isFib B)
  (box : OpenBox T (⟪ σ ⟫ r) (Σᴵ A B))
  where

  module T = ΣLift α β box
  module S = ΣLift (reindex α ⟪ σ ⟫) (reindex β (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  varyA : reshapeFiller σ T.fillA ≡ S.fillA
  varyA = fillerExt (α .vary S T σ r id T.boxA)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    Σext
      (α .vary S T σ r id T.boxA s)
      (adjustSubstEq (curry B (⟪ σ ⟫ s))
         refl refl
         (α .vary S T σ r id T.boxA s)
         (cong (λ cA → cA .fill s .out) varyA)
         (β .vary S T σ r (id ,, out ∘ T.fillA .fill) (T.boxB T.fillA) s)
       ∙ sym (substCongAssoc (curry B (⟪ σ ⟫ s)) (λ cA → cA .fill s .out) varyA _)
       ∙ congdep (λ cA → S.fillB cA .fill s .out) varyA)

opaque
  ΣIsFib : {Γ : Type ℓ}
    {A : Γ → Type ℓ'}
    {B : (Σ x ∈ Γ , A x) → Type ℓ''}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Σᴵ A B)
  ΣIsFib α β .lift S r p = ΣLift.filler (reindex α p) (reindex β (p ×id))
  ΣIsFib α β .vary S T σ r p = ΣVary.eq σ (reindex α p) (reindex β (p ×id))

  ----------------------------------------------------------------------
  -- Forming Σ-types is stable under reindexing
  ----------------------------------------------------------------------
  reindexΣ : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A : Γ → Type ℓ''}
    {B : Σ Γ A → Type ℓ'''}
    (α : isFib A)
    (β : isFib B)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (ΣIsFib α β) ρ ≡ ΣIsFib (reindex α ρ) (reindex β (ρ ×id))
  reindexΣ α β ρ = isFibExt λ _ _ _ _ _ → refl

FibΣ : {Γ : Type ℓ}
  (A : Fib ℓ' Γ)
  (B : Fib ℓ'' (Σ x ∈ Γ , fst A x))
  → -----------
  Fib (ℓ' ⊔ ℓ'') Γ
FibΣ (A , α) (B , β) = Σᴵ A B , ΣIsFib α β

reindexFibΣ : {Δ : Type ℓ} {Γ : Type ℓ'}
  (Aα : Fib ℓ'' Γ)
  (Bβ : Fib ℓ''' (Σ Γ (Aα .fst)))
  (ρ : Δ → Γ)
  → ----------------------
  reindexFib (FibΣ Aα Bβ) ρ ≡ FibΣ (reindexFib Aα ρ) (reindexFib Bβ (ρ ×id))
reindexFibΣ (_ , α) (_ , β) ρ = Σext refl (reindexΣ α β ρ)
