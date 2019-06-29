{-

Composition structures on the union of partially defined types

-}
{-# OPTIONS --rewriting #-}
module union where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.products

_∨'_ : ∀ {ℓ} {Γ : Set ℓ} → (φ ψ : Γ → CofProp) → Γ → CofProp
(φ ∨' ψ) x = φ x ∨ ψ x

module FibUnionId (S : Shape) (φ₀ φ₁ : ⟨ S ⟩ → CofProp)
  {A : res ⟨ S ⟩ (φ₀ ∨' φ₁) → Set}
  (α₀ : isFib (A ∘ id× (∣_∣ ∘ inl)))
  (α₁ : isFib (A ∘ id× (∣_∣ ∘ inr)))
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

module _ {ℓ} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  {A : res Γ (λ x → φ₀ x ∨ φ₁ x) → Set}
  (α₀ : isFib (A ∘ id× (∣_∣ ∘ inl)))
  (α₁ : isFib (A ∘ id× (∣_∣ ∘ inr)))
  (eqFib : reindex' (_ , α₀) (id× fst) ≡ reindex' (_ , α₁) (id× snd))
  where

  FibUnion : isFib A
  FibUnion .lift S r p ψ f x₀ =
    record
    { comp = λ s → compSys s (cntd S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
    ; cap = capSys (cntd S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
    }
    where
    open FibUnionId S
      (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
      {A = A ∘ (fst ∘ p) ×id}
      (reindex (A ∘ id× (∣_∣ ∘ inl)) α₀ ((fst ∘ p) ×id))
      (reindex (A ∘ id× (∣_∣ ∘ inr)) α₁ ((fst ∘ p) ×id))
      (cong (λ Aα → reindex' Aα ((fst ∘ p) ×id)) eqFib)
      (snd ∘ p)
      r ψ f x₀

  FibUnion .vary S T σ r p ψ f x₀ s =
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
                      (reindex (A ∘ id× (∣_∣ ∘ inl)) α₀ (λ s → p (⟪ σ ⟫ s) .fst , u₀ (⟪ σ ⟫ s))))
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
                    (reindex (A ∘ id× (∣_∣ ∘ inl)) α₀ (λ t → p t .fst , u₀ t))))))
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
                      (reindex (A ∘ id× (∣_∣ ∘ inr)) α₁ (λ s → p (⟪ σ ⟫ s) .fst , u₁ (⟪ σ ⟫ s))))
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
                    (reindex (A ∘ id× (∣_∣ ∘ inr)) α₁ (λ t → p t .fst , u₁ t))))))
            (subst (λ u' → isFib (λ t → A (p t .fst , u' t))) (funext λ s → trunc _ _)
              (reindex _ α₁ (λ t → p t .fst , u₁ t))
              .vary S T σ r id ψ f x₀ s)))
      (cntd T (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
    where
    module S = FibUnionId S
      (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫)  (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫)
      {A = A ∘ (fst ∘ p ∘ ⟪ σ ⟫) ×id}
      (reindex (A ∘ id× (∣_∣ ∘ inl)) α₀ ((fst ∘ p ∘ ⟪ σ ⟫) ×id))
      (reindex (A ∘ id× (∣_∣ ∘ inr)) α₁ ((fst ∘ p ∘ ⟪ σ ⟫) ×id))
      (cong (λ Aα → reindex' Aα ((fst ∘ p ∘ ⟪ σ ⟫) ×id)) eqFib)
      (snd ∘ p ∘ ⟪ σ ⟫)
      r ψ (f ◇ ⟪ σ ⟫) x₀

    module T = FibUnionId T
      (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
      {A = A ∘ (fst ∘ p) ×id}
      (reindex (A ∘ id× (∣_∣ ∘ inl)) α₀ ((fst ∘ p) ×id))
      (reindex (A ∘ id× (∣_∣ ∘ inr)) α₁ ((fst ∘ p) ×id))
      (cong (λ Aα → reindex' Aα ((fst ∘ p) ×id)) eqFib)
      (snd ∘ p)
      (⟪ σ ⟫ r) ψ f x₀

  FibUnionL : reindex A FibUnion (id× (∣_∣ ∘ inl)) ≡ α₀
  FibUnionL = fibExt λ S r p ψ f x₀ s →
    let
      open FibUnionId S
        (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        {A = A ∘ (fst ∘ p) ×id}
        (reindex (A ∘ id× (∣_∣ ∘ inl)) α₀ ((fst ∘ p) ×id))
        (reindex (A ∘ id× (∣_∣ ∘ inr)) α₁ ((fst ∘ p) ×id))
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

  FibUnionR : reindex A FibUnion (id× (∣_∣ ∘ inr)) ≡ α₁
  FibUnionR = fibExt λ S r p ψ f x₀ s →
    let
      open FibUnionId S
        (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        {A = A ∘ (fst ∘ p) ×id}
        (reindex (A ∘ id× (∣_∣ ∘ inl)) α₀ ((fst ∘ p) ×id))
        (reindex (A ∘ id× (∣_∣ ∘ inr)) α₁ ((fst ∘ p) ×id))
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

-- TODO: commutes with substitution