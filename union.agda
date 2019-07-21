{-

Composition structures on the union of partially defined types

-}
{-# OPTIONS --rewriting #-}
module union where

open import prelude
open import shape
open import cofprop
open import fibrations
open import Data.products

_∨'_ : ∀ {ℓ} {Γ : Set ℓ} → (φ ψ : Γ → CofProp) → Γ → CofProp
(φ ∨' ψ) x = φ x ∨ ψ x

inl' : ∀ {ℓ} {Γ : Set ℓ} (φ ψ : Γ → CofProp) → res Γ φ → res Γ (φ ∨' ψ)
inl' φ ψ (x , u) = x , ∣ inl u ∣

inr' : ∀ {ℓ} {Γ : Set ℓ} (φ ψ : Γ → CofProp) → res Γ ψ → res Γ (φ ∨' ψ)
inr' φ ψ (x , u) = x , ∣ inr u ∣

----------------------------------------------------------------------
-- Equality of fibration structures on a union of families
----------------------------------------------------------------------
unionFibExt : ∀ {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  {A : res Γ (φ₀ ∨' φ₁) → Set ℓ'} {α₀ α₁ : isFib A}
  → reindex A α₀ (inl' φ₀ φ₁) ≡ reindex A α₁ (inl' φ₀ φ₁)
  → reindex A α₀ (inr' φ₀ φ₁) ≡ reindex A α₁ (inr' φ₀ φ₁)
  → α₀ ≡ α₁
unionFibExt {Γ = Γ} φ₀ φ₁ {A} {α₀} {α₁} eq₀ eq₁ =
  fibExt λ S r p ψ f x₀ s →
    lemma S r p ψ f x₀ s (cntd S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
  where
  module _ (S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → res Γ (φ₀ ∨' φ₁))
    (ψ : CofProp) (f : [ ψ ] → Π (A ∘ p)) (x₀ : A (p r) [ ψ ↦ f ◆ r ]) (s : ⟨ S ⟩)
    where
    move : (u : [ all S ((φ₀ ∨' φ₁) ∘ fst ∘ p) ]) (eq : u ≡ λ i → p i .snd)
      (β : isFib (λ i → A (p i .fst , u i)))
      → A (p s)
    move _ refl β = β .lift S r id ψ f x₀ .comp s .fst

    moveEq : (u : [ all S ((φ₀ ∨' φ₁) ∘ fst ∘ p) ]) (eq : u ≡ λ i → p i .snd) (β : isFib A)
      → β .lift S r p ψ f x₀ .comp s .fst ≡ move u eq (reindex A β (λ i → p i .fst , u i))
    moveEq _ refl β = refl

    lemma : [ all S (φ₀ ∘ fst ∘ p) ∨ all S (φ₁ ∘ fst ∘ p) ]
      → α₀ .lift S r p ψ f x₀ .comp s .fst ≡ α₁ .lift S r p ψ f x₀ .comp s .fst
    lemma =
      ∨-elimEq (all S (φ₀ ∘ fst ∘ p)) (all S (φ₁ ∘ fst ∘ p))
        (λ u₀ →
          trans
            (trans
              (symm (moveEq (λ s → ∣ inl (u₀ s) ∣) (funext λ _ → trunc _ _) α₁))
              (cong
                (λ β →
                  move (λ s → ∣ inl (u₀ s) ∣) (funext λ _ → trunc _ _)
                    (reindex _ β (λ i → p i .fst , u₀ i)))
                eq₀))
            (moveEq (λ s → ∣ inl (u₀ s) ∣) (funext λ _ → trunc _ _) α₀))
        (λ u₁ →
          trans
            (trans
              (symm (moveEq (λ s → ∣ inr (u₁ s) ∣) (funext λ _ → trunc _ _) α₁))
              (cong
                (λ β →
                  move (λ s → ∣ inr (u₁ s) ∣) (funext λ _ → trunc _ _)
                    (reindex _ β (λ i → p i .fst , u₁ i)))
                eq₁))
            (moveEq (λ s → ∣ inr (u₁ s) ∣) (funext λ _ → trunc _ _) α₀))

unionFibExt' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  {Aα₀ Aα₁ : Fib ℓ' (res Γ (φ₀ ∨' φ₁))}
  → reindex' Aα₀ (inl' φ₀ φ₁) ≡ reindex' Aα₁ (inl' φ₀ φ₁)
  → reindex' Aα₀ (inr' φ₀ φ₁) ≡ reindex' Aα₁ (inr' φ₀ φ₁)
  → Aα₀ ≡ Aα₁
unionFibExt' {Γ = Γ} φ₀ φ₁ {Aα₀} {Aα₁} eq₀ eq₁ =
  lemma
    (funext
      (uncurry λ x → ∨-elimEq (φ₀ x) (φ₁ x)
        (λ u₀ → cong (λ Bβ → Bβ .fst (x , u₀)) eq₀)
        (λ u₁ → cong (λ Bβ → Bβ .fst (x , u₁)) eq₁)))
  where
  lemma : Aα₀ .fst ≡ Aα₁ .fst → Aα₀ ≡ Aα₁
  lemma refl =
    cong (λ β → Aα₁ .fst , β)
      (unionFibExt φ₀ φ₁
        (Σeq₂' eq₀ refl)
        (Σeq₂' eq₁ refl))

-- ----------------------------------------------------------------------
-- Deriving a fibrancy structure on a union
----------------------------------------------------------------------

module FibUnionId {ℓ} (S : Shape) (φ₀ φ₁ : ⟨ S ⟩ → CofProp)
  (A : res ⟨ S ⟩ (φ₀ ∨' φ₁) → Set ℓ)
  (α₀ : isFib (A ∘ inl' φ₀ φ₁))
  (α₁ : isFib (A ∘ inr' φ₀ φ₁))
  (eqFib : reindex' (_ , α₀) (id× fst) ≡ reindex' (_ , α₁) (id× snd))
  (u : ∀ s → [ φ₀ s ∨ φ₁ s ])
  (r : ⟨ S ⟩) (ψ : CofProp)
  (f : [ ψ ] → (s : ⟨ S ⟩) → A (s , u s))
  (x₀ : A (r , u r) [ ψ ↦ f ◆ r ])
  where

  compSys : ∀ s → [ all S φ₀ ∨ all S φ₁ ] → A (s , u s) [ ψ ↦ f ◆ s ]
  compSys s =
    ∨-rec (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₀ (λ s → s , u₀ s))
          .lift S r id ψ f x₀ .comp s)
      (λ u₁ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₁ (λ s → s , u₁ s))
          .lift S r id ψ f x₀ .comp s)
      (λ u₀ u₁ →
        cong
          (λ {(u' , α') →
            subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc (u' s) _) α'
              .lift S r id ψ f x₀ .comp s})
          (Σext
            (funext λ _ → trunc _ _)
            (trans
              (Σeq₂'
                (cong (λ Aα' → reindex' Aα' (λ s → (s , u₀ s , u₁ s))) eqFib)
                (cong (λ u' s → A (s , u' s)) (funext λ _ → trunc _ _)))
              (substCongAssoc isFib (λ u' s → A (s , u' s))
                (funext λ s → trunc _ _) _))))

  capSys : (u : [ all S φ₀ ∨ all S φ₁ ]) → compSys r u .fst ≡ x₀ .fst
  capSys =
    ∨-elimEq (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₀ (λ s → s , u₀ s))
          .lift S r id ψ f x₀ .cap)
      (λ u₁ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₁ (λ s → s , u₁ s))
          .lift S r id ψ f x₀ .cap)

module FibUnion {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  (A : res Γ (φ₀ ∨' φ₁) → Set ℓ')
  (α₀ : isFib (A ∘ inl' φ₀ φ₁))
  (α₁ : isFib (A ∘ inr' φ₀ φ₁))
  (eqFib : reindex' (_ , α₀) (id× fst) ≡ reindex' (_ , α₁) (id× snd))
  where

  abstract

    fib : isFib A
    fib .lift S r p ψ f x₀ =
      record
      { comp = λ s → compSys s (cntd S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
      ; cap = capSys (cntd S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
      }
      where
      open FibUnionId S (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
        (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
        (cong (λ Aα → reindex' Aα ((fst ∘ p) ×id)) eqFib)
        (snd ∘ p)
        r ψ f x₀

    fib .vary S T σ r p ψ f x₀ s =
      ∨-elimEq (all T (φ₀ ∘ fst ∘ p)) (all T (φ₁ ∘ fst ∘ p))
        {f = λ u → T.compSys (⟪ σ ⟫ s) u .fst}
        {g = λ _ → S.compSys s (cntd S (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫) (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫) (snd ∘ p ∘ ⟪ σ ⟫)) .fst}
        (λ u₀ →
          trans
            (cong (λ u' → S.compSys s u' .fst)
              (trunc ∣ inl (λ s → u₀ (⟪ σ ⟫ s)) ∣
                (cntd S (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫) (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫) (snd ∘ p ∘ ⟪ σ ⟫))))
            (trans
              (cong (λ α → α .lift S r id ψ (f ◇ ⟪ σ ⟫) x₀ .comp s .fst)
                (trans
                  (cong
                    (λ eq →
                      subst (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s))) eq
                        (reindex (A ∘ inl' φ₀ φ₁) α₀ (λ s → p (⟪ σ ⟫ s) .fst , u₀ (⟪ σ ⟫ s))))
                    (uip
                      (cong (λ u' → u' ∘ ⟪ σ ⟫) (funext λ t → trunc _ (p t .snd)))
                      (funext λ s → trunc _ (p (⟪ σ ⟫ s) .snd))))
                  (trans
                    (substCongAssoc
                      (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s)))
                      (λ u' → u' ∘ ⟪ σ ⟫)
                      (funext λ t → trunc _ _)
                      (reindex _ α₀ (λ s → p (⟪ σ ⟫ s) .fst , u₀ (⟪ σ ⟫ s))))
                    (substNaturality
                      (λ u' → isFib (λ t → A (p t .fst , u' t)))
                      (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' (⟪ σ ⟫ s))))
                      (λ u' α → reindex _ α ⟪ σ ⟫)
                      (funext λ t → trunc ∣ inl (u₀ t) ∣ (p t .snd))
                      (reindex (A ∘ inl' φ₀ φ₁) α₀ (λ t → p t .fst , u₀ t))))))
              (subst (λ u' → isFib (λ t → A (p t .fst , u' t))) (funext λ s → trunc _ _)
                (reindex _ α₀ (λ t → p t .fst , u₀ t))
                .vary S T σ r id ψ f x₀ s)))
        (λ u₁ →
          trans
            (cong (λ u' → S.compSys s u' .fst)
              (trunc ∣ inr (λ s → u₁ (⟪ σ ⟫ s)) ∣
                (cntd S (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫) (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫) (snd ∘ p ∘ ⟪ σ ⟫))))
            (trans
              (cong (λ α → α .lift S r id ψ (f ◇ ⟪ σ ⟫) x₀ .comp s .fst)
                (trans
                  (cong
                    (λ eq →
                      subst (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s))) eq
                        (reindex (A ∘ inr' φ₀ φ₁) α₁ (λ s → p (⟪ σ ⟫ s) .fst , u₁ (⟪ σ ⟫ s))))
                    (uip
                      (cong (λ u' → u' ∘ ⟪ σ ⟫) (funext λ t → trunc _ (p t .snd)))
                      (funext λ s → trunc _ (p (⟪ σ ⟫ s) .snd))))
                  (trans
                    (substCongAssoc
                      (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s)))
                      (λ u' → u' ∘ ⟪ σ ⟫)
                      (funext λ t → trunc _ _)
                      (reindex _ α₁ (λ s → p (⟪ σ ⟫ s) .fst , u₁ (⟪ σ ⟫ s))))
                    (substNaturality
                      (λ u' → isFib (λ t → A (p t .fst , u' t)))
                      (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' (⟪ σ ⟫ s))))
                      (λ u' α → reindex _ α ⟪ σ ⟫)
                      (funext λ t → trunc ∣ inr (u₁ t) ∣ (p t .snd))
                      (reindex (A ∘ inr' φ₀ φ₁) α₁ (λ t → p t .fst , u₁ t))))))
              (subst (λ u' → isFib (λ t → A (p t .fst , u' t))) (funext λ s → trunc _ _)
                (reindex _ α₁ (λ t → p t .fst , u₁ t))
                .vary S T σ r id ψ f x₀ s)))
        (cntd T (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
      where
      module S = FibUnionId S (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫)  (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫)
        (A ∘ (fst ∘ p ∘ ⟪ σ ⟫) ×id)
        (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p ∘ ⟪ σ ⟫) ×id))
        (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p ∘ ⟪ σ ⟫) ×id))
        (cong (λ Aα → reindex' Aα ((fst ∘ p ∘ ⟪ σ ⟫) ×id)) eqFib)
        (snd ∘ p ∘ ⟪ σ ⟫)
        r ψ (f ◇ ⟪ σ ⟫) x₀

      module T = FibUnionId T (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
        (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
        (cong (λ Aα → reindex' Aα ((fst ∘ p) ×id)) eqFib)
        (snd ∘ p)
        (⟪ σ ⟫ r) ψ f x₀

    left : reindex A fib (inl' φ₀ φ₁) ≡ α₀
    left = fibExt λ S r p ψ f x₀ s →
      let
        open FibUnionId S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
          (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
          (cong (λ Aα → reindex' Aα ((fst ∘ p) ×id)) eqFib)
          (λ s → ∣ inl (p s .snd) ∣)
          r ψ f x₀
      in
      trans
        (cong
          (λ eq →
            subst (λ u' → isFib (λ s → A (p s .fst , u' s))) eq (reindex _ α₀ p)
              .lift S r id ψ f x₀ .comp s .fst)
          (uip (funext λ _ → trunc _ _) refl))
        (cong (fst ∘ compSys s)
          (trunc
            (cntd S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (λ s → ∣ inl (p s .snd) ∣))
            (∣ inl (λ s → p s .snd) ∣)))

    right : reindex A fib (inr' φ₀ φ₁) ≡ α₁
    right = fibExt λ S r p ψ f x₀ s →
      let
        open FibUnionId S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
          (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
          (cong (λ Aα → reindex' Aα ((fst ∘ p) ×id)) eqFib)
          (λ s → ∣ inr (p s .snd) ∣)
          r ψ f x₀
      in
      trans
        (cong
          (λ eq →
            subst (λ u' → isFib (λ s → A (p s .fst , u' s))) eq (reindex _ α₁ p)
              .lift S r id ψ f x₀ .comp s .fst)
          (uip (funext λ _ → trunc _ _) refl))
        (cong (fst ∘ compSys s)
          (trunc
            (cntd S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (λ s → ∣ inr (p s .snd) ∣))
            (∣ inr (λ s → p s .snd) ∣)))

reindexUnion : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (A : res Γ (φ₀ ∨' φ₁) → Set ℓ'')
  (α₀ : isFib (A ∘ inl' φ₀ φ₁))
  (α₁ : isFib (A ∘ inr' φ₀ φ₁))
  (eqFib : reindex' (_ , α₀) (id× fst) ≡ reindex' (_ , α₁) (id× snd))
  (ρ : Δ → Γ)
  → reindex A (FibUnion.fib φ₀ φ₁ A α₀ α₁ eqFib) (ρ ×id)
    ≡ FibUnion.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (A ∘ ρ ×id)
      (reindex _ α₀ (ρ ×id)) (reindex _ α₁ (ρ ×id)) (cong (reindex' ◆ (ρ ×id)) eqFib)
reindexUnion φ₀ φ₁ A α₀ α₁ eqFib ρ =
  unionFibExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (trans
      (symm (FibUnion.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))
      (cong (reindex (A ∘ inl' φ₀ φ₁) ◆ (ρ ×id)) (FibUnion.left φ₀ φ₁ A α₀ α₁ eqFib)))
    (trans
      (symm (FibUnion.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))
      (cong (reindex (A ∘ inr' φ₀ φ₁) ◆ (ρ ×id)) (FibUnion.right φ₀ φ₁ A α₀ α₁ eqFib)))

module UnionFib {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  (Aα₀ : Fib ℓ' (res Γ φ₀)) (Aα₁ : Fib ℓ' (res Γ φ₁))
  (eqFib : reindex' Aα₀ (id× fst) ≡ reindex' Aα₁ (id× snd))
  where

  private
    module F = FibUnion φ₀ φ₁
      (uncurry λ x →
        ∨-rec (φ₀ x) (φ₁ x)
          (curry (Aα₀ .fst) x)
          (curry (Aα₁ .fst) x)
          (λ u₀ u₁ → cong (λ Bβ → Bβ .fst (x , u₀ , u₁)) eqFib))
      (Aα₀ .snd)
      (Aα₁ .snd)
      eqFib

  abstract
    fib : Fib ℓ' (res Γ (φ₀ ∨' φ₁))
    fib = (_ , F.fib)

    left : reindex' fib (inl' φ₀ φ₁) ≡ Aα₀
    left = cong (λ f → Aα₀ .fst , f) F.left

    right : reindex' fib (inr' φ₀ φ₁) ≡ Aα₁
    right = cong (λ f → Aα₁ .fst , f) F.right

reindexUnion' : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (Aα₀ : Fib ℓ'' (res Γ φ₀)) (Aα₁ : Fib ℓ'' (res Γ φ₁))
  (eqFib : reindex' Aα₀ (id× fst) ≡ reindex' Aα₁ (id× snd))
  (ρ : Δ → Γ)
  → reindex' (UnionFib.fib φ₀ φ₁ Aα₀ Aα₁ eqFib) (ρ ×id)
    ≡ UnionFib.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (reindex' Aα₀ (ρ ×id)) (reindex' Aα₁ (ρ ×id))
        (cong (reindex' ◆ (ρ ×id)) eqFib)
reindexUnion' {Δ = Δ} φ₀ φ₁ Aα₀ Aα₁ eqFib ρ =
  unionFibExt' (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (trans
      (symm (UnionFib.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
      (cong (reindex' ◆ (ρ ×id)) (UnionFib.left φ₀ φ₁ Aα₀ Aα₁ eqFib)))
    (trans
      (symm (UnionFib.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
      (cong (reindex' ◆ (ρ ×id)) (UnionFib.right φ₀ φ₁ Aα₀ Aα₁ eqFib)))
