{-

Fibration structure on Π-types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.pi where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.coercion

private variable ℓ ℓ' ℓ'' ℓ''' : Level

Π' : {Γ : Set ℓ} (A : Γ → Set ℓ') (B : (Σ x ∈ Γ , A x) → Set ℓ'')
  → Γ → Set (ℓ' ⊔ ℓ'')
Π' A B x = (a : A x) → B (x , a)

module ΠLift {S r}
  {A : ⟨ S ⟩ → Set ℓ} {B : Σ ⟨ S ⟩ A → Set ℓ'}
  (α : isFib A) (β : isFib B)
  (box : OpenBox S r (Π' A B))
  where

  module _ (s : ⟨ S ⟩) (a : A s) where

    fillA = coerceFiller S s α a
    coeA = coerce S s α a

    module _ (coerceA : (i : ⟨ S ⟩) → A i) where

      boxB : OpenBox S r (B ∘ (id ,, coerceA))
      boxB = mapBox (λ i f → f (coerceA i)) box

      fillB = β .lift S r (id ,, coerceA) boxB

  filler : Filler box
  filler .fill s .out a =
    subst (curry B s)
      (fillA s a .cap≡)
      (fillB s a (coeA s a) .fill s .out)
  filler .fill s .out≡ u =
    funext λ a →
    sym (congdep (box .tube u s) (fillA s a .cap≡))
    ∙ cong (subst (curry B s) (fillA s a .cap≡))
        (fillB s a (coeA s a) .fill s .out≡ u)
  filler .cap≡ =
    funext λ a →
    cong (subst (curry B r) (fillA r a .cap≡))
      (fillB r a (coeA r a) .cap≡)
    ∙ congdep (box .cap .out) (fillA r a .cap≡)

module ΠVary {S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ → Set ℓ} {B : Σ ⟨ T ⟩ A → Set ℓ'}
  (α : isFib A) (β : isFib B)
  (box : OpenBox T (⟪ σ ⟫ r) (Π' A B))
  where

  module T = ΠLift α β box
  module S = ΠLift (reindex α ⟪ σ ⟫) (reindex β (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  varyA : ∀ s a i → T.coeA (⟪ σ ⟫ s) a (⟪ σ ⟫ i) ≡ S.coeA s a i
  varyA s = coerceVary S T σ s α

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    funext λ a →
    cong
      (subst (curry B (⟪ σ ⟫ s)) (T.fillA _ a .cap≡))
      (β .vary S T σ r (id ,, T.coeA _ a) (T.boxB _ a (T.coeA _ a)) s)
    ∙
    adjustSubstEq (curry B (⟪ σ ⟫ s))
      (appCong (funext (varyA s a))) refl
      (T.fillA (⟪ σ ⟫ s) a .cap≡) (S.fillA s a .cap≡)
      (sym (substCongAssoc (curry B (⟪ σ ⟫ s)) (λ cA → cA s) (funext (varyA s a)) _)
        ∙ congdep (λ cA → S.fillB s a cA .fill s .out) (funext (varyA s a)))

opaque
  ΠIsFib : {Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    {B : (Σ x ∈ Γ , A x) → Set ℓ''}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Π' A B)
  ΠIsFib α β .lift S r p = ΠLift.filler (reindex α p) (reindex β (p ×id))
  ΠIsFib α β .vary S T σ r p = ΠVary.eq σ (reindex α p) (reindex β (p ×id))

  ----------------------------------------------------------------------
  -- Forming Π-types is stable under reindexing
  ----------------------------------------------------------------------
  reindexΠ : {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set ℓ''}
    {B : Σ Γ A → Set ℓ'''}
    (α : isFib A)
    (β : isFib B)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (ΠIsFib α β) ρ ≡ ΠIsFib (reindex α ρ) (reindex β (ρ ×id))
  reindexΠ α β ρ = isFibExt λ _ _ _ _ _ → refl

FibΠ : {Γ : Set ℓ}
  (A : Fib ℓ' Γ)
  (B : Fib ℓ'' (Σ x ∈ Γ , fst A x))
  → -----------
  Fib (ℓ' ⊔ ℓ'') Γ
FibΠ (A , α) (B , β) = (Π' A B , ΠIsFib α β)

reindexFibΠ : {Δ : Set ℓ} {Γ : Set ℓ'}
  (Aα : Fib ℓ'' Γ)
  (Bβ : Fib ℓ''' (Σ Γ (Aα .fst)))
  (ρ : Δ → Γ)
  → ----------------------
  reindexFib (FibΠ Aα Bβ) ρ ≡ FibΠ (reindexFib Aα ρ) (reindexFib Bβ (ρ ×id))
reindexFibΠ (_ , α) (_ , β) ρ = Σext refl (reindexΠ α β ρ)
