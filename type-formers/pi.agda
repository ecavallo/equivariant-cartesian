{-

Fibration structure on Π-types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.pi where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.coercion

Π' : ∀{ℓ ℓ' ℓ''} {Γ : Set ℓ}(A : Γ → Set ℓ')(B : (Σ x ∈ Γ , A x) → Set ℓ'')
  → Γ → Set (ℓ' ⊔ ℓ'')
Π' A B x = (a : A x) → B (x , a)

module ΠIsFibId {ℓ ℓ'}
  {S : Shape} {A : ⟨ S ⟩ → Set ℓ} {B : Σ ⟨ S ⟩ A → Set ℓ'}
  (α : isFib A) (β : isFib B)
  {r : ⟨ S ⟩} (box : OpenBox S r (Π' A B))
  where

  module _ (s : ⟨ S ⟩) (a : A s) where

    fillA = coerceFiller S s α a

    module _ (coerceA : (i : ⟨ S ⟩) → A i) where

      q : ⟨ S ⟩ → Σ ⟨ S ⟩ A
      q i = (i , coerceA i)

      boxB : OpenBox S r (B ∘ q)
      boxB = mapBox (λ i f → f (coerceA i)) box

      fillB = β .lift S r q boxB

opaque
  ΠIsFib :
    ∀{ℓ ℓ' ℓ''}{Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    {B : (Σ x ∈ Γ , A x) → Set ℓ''}
    (α : isFib A)
    (β : isFib B)
    → -----------
    isFib (Π' A B)
  ΠIsFib {B = B} α β .lift S r p box = filler
    where
    open ΠIsFibId (reindex α p) (reindex β (p ×id)) box

    filler : Filler box
    filler .fill s .out a =
      subst (curry B (p s))
        (fillA s a .cap≡)
        (fillB s a (out ∘ fillA s a .fill) .fill s .out)
    filler .fill s .out≡ u =
      funext λ a →
      symm (congdep (box .tube u s) (fillA s a .cap≡))
      ∙ cong (subst (curry B (p s)) (fillA s a .cap≡))
          (fillB s a (out ∘ fillA s a .fill) .fill s .out≡ u)
    filler .cap≡ =
      funext λ a →
      cong (subst (curry B (p r)) (fillA r a .cap≡))
        (fillB r a (out ∘ fillA r a .fill) .cap≡)
      ∙ congdep (box .cap .out) (fillA r a .cap≡)

  ΠIsFib {B = B} α β .vary S T σ r p box s =
    funext λ a →
    cong
      (subst (curry B (p (⟪ σ ⟫ s))) (T.fillA _ a .cap≡))
      (β .vary S T σ r (p ×id ∘ T.q _ a (out ∘ T.fillA _ a .fill)) (T.boxB _ a (out ∘ T.fillA _ a .fill)) s)
    ∙
    adjustSubstEq (curry B (p (⟪ σ ⟫ s)))
      (cong (λ cA → S.q s a cA s .snd) (funext (varyA a))) refl
      (T.fillA (⟪ σ ⟫ s) a .cap≡) (S.fillA s a .cap≡)
      (symm (substCongAssoc (curry B (p (⟪ σ ⟫ s))) (λ cA → S.q s a cA s .snd) (funext (varyA a)) _)
        ∙ congdep (λ cA → S.fillB s a cA .fill s .out) (funext (varyA a)))
    where
    module T = ΠIsFibId (reindex α p) (reindex β (p ×id)) box
    module S = ΠIsFibId (reindex α (p ∘ ⟪ σ ⟫)) (reindex β ((p ∘ ⟪ σ ⟫) ×id)) (reshapeBox σ box)

    varyA : ∀ a i → T.fillA _ a .fill _ .out ≡ S.fillA s a .fill i .out
    varyA = coerceVary S T σ s (reindex α p)

  ----------------------------------------------------------------------
  -- Forming Π-types is stable under reindexing
  ----------------------------------------------------------------------
  reindexΠ : ∀ {ℓ ℓ' ℓ'' ℓ'''}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set ℓ''}
    {B : Σ Γ A → Set ℓ'''}
    (α : isFib A)
    (β : isFib B)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (ΠIsFib α β) ρ ≡ ΠIsFib (reindex α ρ) (reindex β (ρ ×id))
  reindexΠ α β ρ = isFibExt λ _ _ _ _ _ → refl

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
reindexFibΠ (_ , α) (_ , β) ρ = Σext refl (reindexΠ α β ρ)
