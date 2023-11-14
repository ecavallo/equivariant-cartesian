{-

Composition structures on the union of partially defined types (i.e., a system of types)

-}
{-# OPTIONS --rewriting #-}
module type-formers.union where

open import prelude
open import axioms
open import fibration.fibration

_∨'_ : ∀ {ℓ} {Γ : Set ℓ} → (φ ψ : Γ → CofProp) → Γ → CofProp
(φ ∨' ψ) x = φ x ∨ ψ x

inl' : ∀ {ℓ} {Γ : Set ℓ} (φ ψ : Γ → CofProp) → Γ ,[ φ ] → Γ ,[ φ ∨' ψ ]
inl' φ ψ (x , u) = x , ∣ inl u ∣

inr' : ∀ {ℓ} {Γ : Set ℓ} (φ ψ : Γ → CofProp) → Γ ,[ ψ ] → Γ ,[ φ ∨' ψ ]
inr' φ ψ (x , u) = x , ∣ inr u ∣

----------------------------------------------------------------------
-- Equality of fibration structures on a union of families
----------------------------------------------------------------------
unionIsFibExt : ∀ {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  {A : Γ ,[ φ₀ ∨' φ₁ ] → Set ℓ'} {α₀ α₁ : isFib A}
  → reindex A α₀ (inl' φ₀ φ₁) ≡ reindex A α₁ (inl' φ₀ φ₁)
  → reindex A α₀ (inr' φ₀ φ₁) ≡ reindex A α₁ (inr' φ₀ φ₁)
  → α₀ ≡ α₁
unionIsFibExt {Γ = Γ} φ₀ φ₁ {A} {α₀} {α₁} eq₀ eq₁ =
  isFibExt λ S r p box s →
    lemma S r p box s (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
  where
  module _ (S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → Γ ,[ φ₀ ∨' φ₁ ]) (box : OpenBox S r (A ∘ p)) (s : ⟨ S ⟩)
    where
    move : (u : [ all S ((φ₀ ∨' φ₁) ∘ fst ∘ p) ]) (eq : u ≡ λ i → p i .snd)
      (β : isFib (λ i → A (p i .fst , u i)))
      → A (p s)
    move _ refl β = β .lift S r id box .fill s .out

    moveEq : (u : [ all S ((φ₀ ∨' φ₁) ∘ fst ∘ p) ]) (eq : u ≡ λ i → p i .snd) (β : isFib A)
      → β .lift S r p box .fill s .out ≡ move u eq (reindex A β (λ i → p i .fst , u i))
    moveEq _ refl β = refl

    lemma : [ all S (φ₀ ∘ fst ∘ p) ∨ all S (φ₁ ∘ fst ∘ p) ]
      → α₀ .lift S r p box .fill s .out ≡ α₁ .lift S r p box .fill s .out
    lemma =
      ∨-elimEq (all S (φ₀ ∘ fst ∘ p)) (all S (φ₁ ∘ fst ∘ p))
        (λ u₀ →
          moveEq (λ s → ∣ inl (u₀ s) ∣) (funext λ _ → trunc _ _) α₀
          ∙ cong
                (λ β →
                  move (λ s → ∣ inl (u₀ s) ∣) (funext λ _ → trunc _ _)
                    (reindex _ β (λ i → p i .fst , u₀ i)))
                eq₀
          ∙ symm (moveEq (λ s → ∣ inl (u₀ s) ∣) (funext λ _ → trunc _ _) α₁))
        (λ u₁ →
          moveEq (λ s → ∣ inr (u₁ s) ∣) (funext λ _ → trunc _ _) α₀
          ∙ cong
                (λ β →
                  move (λ s → ∣ inr (u₁ s) ∣) (funext λ _ → trunc _ _)
                    (reindex _ β (λ i → p i .fst , u₁ i)))
                eq₁
          ∙ symm (moveEq (λ s → ∣ inr (u₁ s) ∣) (funext λ _ → trunc _ _) α₁))

unionFibExt : ∀ {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  {Aα₀ Aα₁ : Fib ℓ' (Γ ,[ φ₀ ∨' φ₁ ])}
  → reindexFib Aα₀ (inl' φ₀ φ₁) ≡ reindexFib Aα₁ (inl' φ₀ φ₁)
  → reindexFib Aα₀ (inr' φ₀ φ₁) ≡ reindexFib Aα₁ (inr' φ₀ φ₁)
  → Aα₀ ≡ Aα₁
unionFibExt {Γ = Γ} φ₀ φ₁ {Aα₀} {Aα₁} eq₀ eq₁ =
  lemma
    (funext
      (uncurry λ x → ∨-elimEq (φ₀ x) (φ₁ x)
        (λ u₀ → cong (λ Bβ → Bβ .fst (x , u₀)) eq₀)
        (λ u₁ → cong (λ Bβ → Bβ .fst (x , u₁)) eq₁)))
  where
  lemma : Aα₀ .fst ≡ Aα₁ .fst → Aα₀ ≡ Aα₁
  lemma refl =
    cong (λ β → Aα₁ .fst , β)
      (unionIsFibExt φ₀ φ₁
        (Σeq₂ eq₀ refl)
        (Σeq₂ eq₁ refl))

-- ----------------------------------------------------------------------
-- Deriving a fibrancy structure on a union
----------------------------------------------------------------------

module UnionIsFibId {ℓ} {S : Shape} (φ₀ φ₁ : ⟨ S ⟩ → CofProp)
  (A : ⟨ S ⟩ ,[ φ₀ ∨' φ₁ ] → Set ℓ)
  (α₀ : isFib (A ∘ inl' φ₀ φ₁))
  (α₁ : isFib (A ∘ inr' φ₀ φ₁))
  (eqFib : reindexFib (_ , α₀) (id× fst) ≡ reindexFib (_ , α₁) (id× snd))
  {u : ∀ s → [ φ₀ s ∨ φ₁ s ]}
  {r : ⟨ S ⟩}
  (box : OpenBox S r (λ s → A (s , u s)))
  where

  fillSys : ∀ s → [ all S φ₀ ∨ all S φ₁ ] → A (s , u s) [ box .cof ↦ box .tube ◆ s ]
  fillSys s =
    ∨-rec (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₀ (λ s → s , u₀ s))
          .lift S r id box .fill s)
      (λ u₁ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₁ (λ s → s , u₁ s))
          .lift S r id box .fill s)
      (λ u₀ u₁ →
        congΣ
          (λ u' α' →
            subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc (u' s) _) α'
              .lift S r id box .fill s)
          (funext λ _ → trunc _ _)
          (substCongAssoc isFib (λ u' s → A (s , u' s)) (funext λ s → trunc _ _) _
            ∙ Σeq₂
                (cong (λ Aα' → reindexFib Aα' (λ s → (s , u₀ s , u₁ s))) eqFib)
                (cong (λ u' s → A (s , u' s)) (funext λ _ → trunc _ _))))

  capSys : (u : [ all S φ₀ ∨ all S φ₁ ]) → fillSys r u .out ≡ box .cap .out
  capSys =
    ∨-elimEq (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₀ (λ s → s , u₀ s))
          .lift S r id box .cap≡)
      (λ u₁ →
        subst (λ u' → isFib (λ s → A (s , u' s))) (funext λ s → trunc _ _)
          (reindex _ α₁ (λ s → s , u₁ s))
          .lift S r id box .cap≡)

module UnionIsFib {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  (A : Γ ,[ φ₀ ∨' φ₁ ] → Set ℓ')
  (α₀ : isFib (A ∘ inl' φ₀ φ₁))
  (α₁ : isFib (A ∘ inr' φ₀ φ₁))
  (eqFib : reindexFib (_ , α₀) (id× fst) ≡ reindexFib (_ , α₁) (id× snd))
  where

  opaque

    fib : isFib A
    fib .lift S r p box =
      record
      { fill = λ s → fillSys s (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
      ; cap≡ = capSys (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
      }
      where
      open UnionIsFibId (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
        (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
        (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id)) eqFib)
        box

    fib .vary S T σ r p box s =
      ∨-elimEq (all T (φ₀ ∘ fst ∘ p)) (all T (φ₁ ∘ fst ∘ p))
        {f = λ u → T.fillSys (⟪ σ ⟫ s) u .out}
        {g = λ _ → S.fillSys s (shape→∨ S (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫) (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫) (snd ∘ p ∘ ⟪ σ ⟫)) .out}
        (λ u₀ →
          subst (λ u' → isFib (λ t → A (p t .fst , u' t))) (funext λ s → trunc _ _)
            (reindex _ α₀ (λ t → p t .fst , u₀ t))
            .vary S T σ r id box s
          ∙
          cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
            (substNaturality
                  (λ u' → isFib (λ t → A (p t .fst , u' t)))
                  (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' (⟪ σ ⟫ s))))
                  (λ u' α → reindex _ α ⟪ σ ⟫)
                  (funext λ t → trunc ∣ inl (u₀ t) ∣ (p t .snd))
                  (reindex (A ∘ inl' φ₀ φ₁) α₀ (λ t → p t .fst , u₀ t))
             ∙
             substCongAssoc
               (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s)))
               (λ u' → u' ∘ ⟪ σ ⟫)
               (funext λ t → trunc _ _)
               (reindex _ α₀ (λ s → p (⟪ σ ⟫ s) .fst , u₀ (⟪ σ ⟫ s)))
             ∙
             cong
               (λ eq →
                  subst (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s))) eq
                    (reindex (A ∘ inl' φ₀ φ₁) α₀ (λ s → p (⟪ σ ⟫ s) .fst , u₀ (⟪ σ ⟫ s))))
               (uip
                 (cong (λ u' → u' ∘ ⟪ σ ⟫) (funext λ t → trunc _ (p t .snd)))
                 (funext λ s → trunc _ (p (⟪ σ ⟫ s) .snd))))
          ∙
          cong (λ u' → S.fillSys s u' .out)
            (trunc ∣ inl (λ s → u₀ (⟪ σ ⟫ s)) ∣
              (shape→∨ S (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫) (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫) (snd ∘ p ∘ ⟪ σ ⟫))))
        (λ u₁ →
          subst (λ u' → isFib (λ t → A (p t .fst , u' t))) (funext λ s → trunc _ _)
            (reindex _ α₁ (λ t → p t .fst , u₁ t))
            .vary S T σ r id box s
          ∙
          cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
            (substNaturality
              (λ u' → isFib (λ t → A (p t .fst , u' t)))
              (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' (⟪ σ ⟫ s))))
              (λ u' α → reindex _ α ⟪ σ ⟫)
              (funext λ t → trunc ∣ inr (u₁ t) ∣ (p t .snd))
              (reindex (A ∘ inr' φ₀ φ₁) α₁ (λ t → p t .fst , u₁ t))
             ∙
             substCongAssoc
               (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s)))
               (λ u' → u' ∘ ⟪ σ ⟫)
               (funext λ t → trunc _ _)
               (reindex _ α₁ (λ s → p (⟪ σ ⟫ s) .fst , u₁ (⟪ σ ⟫ s)))
             ∙
             cong
               (λ eq →
                 subst (λ u' → isFib (λ s → A (p (⟪ σ ⟫ s) .fst , u' s))) eq
                   (reindex (A ∘ inr' φ₀ φ₁) α₁ (λ s → p (⟪ σ ⟫ s) .fst , u₁ (⟪ σ ⟫ s))))
                   (uip
                     (cong (λ u' → u' ∘ ⟪ σ ⟫) (funext λ t → trunc _ (p t .snd)))
                     (funext λ s → trunc _ (p (⟪ σ ⟫ s) .snd))))
          ∙
          cong (λ u' → S.fillSys s u' .out)
            (trunc ∣ inr (λ s → u₁ (⟪ σ ⟫ s)) ∣
              (shape→∨ S (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫) (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫) (snd ∘ p ∘ ⟪ σ ⟫))))
        (shape→∨ T (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
      where
      module S = UnionIsFibId (φ₀ ∘ fst ∘ p ∘ ⟪ σ ⟫)  (φ₁ ∘ fst ∘ p ∘ ⟪ σ ⟫)
        (A ∘ (fst ∘ p ∘ ⟪ σ ⟫) ×id)
        (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p ∘ ⟪ σ ⟫) ×id))
        (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p ∘ ⟪ σ ⟫) ×id))
        (cong (λ Aα → reindexFib Aα ((fst ∘ p ∘ ⟪ σ ⟫) ×id)) eqFib)
        (reshapeBox σ box)

      module T = UnionIsFibId (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
        (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
        (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id)) eqFib)
        box

    left : reindex A fib (inl' φ₀ φ₁) ≡ α₀
    left = isFibExt λ S r p box s →
      let
        open UnionIsFibId (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
          (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
          (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id)) eqFib)
          box
      in
      cong (out ∘ fillSys s)
        (trunc
          (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (λ s → ∣ inl (p s .snd) ∣))
          (∣ inl (λ s → p s .snd) ∣))
      ∙
      cong
        (λ eq →
          subst (λ u' → isFib (λ s → A (p s .fst , u' s))) eq (reindex _ α₀ p)
            .lift S r id box .fill s .out)
        (uip (funext λ _ → trunc _ _) refl)

    right : reindex A fib (inr' φ₀ φ₁) ≡ α₁
    right = isFibExt λ S r p box s →
      let
        open UnionIsFibId (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (reindex (A ∘ inl' φ₀ φ₁) α₀ ((fst ∘ p) ×id))
          (reindex (A ∘ inr' φ₀ φ₁) α₁ ((fst ∘ p) ×id))
          (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id)) eqFib)
          box
      in
      cong (out ∘ fillSys s)
        (trunc
          (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (λ s → ∣ inr (p s .snd) ∣))
          (∣ inr (λ s → p s .snd) ∣))
      ∙
      cong
        (λ eq →
          subst (λ u' → isFib (λ s → A (p s .fst , u' s))) eq (reindex _ α₁ p)
            .lift S r id box .fill s .out)
        (uip (funext λ _ → trunc _ _) refl)

reindexUnion : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (A : Γ ,[ φ₀ ∨' φ₁ ] → Set ℓ'')
  (α₀ : isFib (A ∘ inl' φ₀ φ₁))
  (α₁ : isFib (A ∘ inr' φ₀ φ₁))
  (eqFib : reindexFib (_ , α₀) (id× fst) ≡ reindexFib (_ , α₁) (id× snd))
  (ρ : Δ → Γ)
  → reindex A (UnionIsFib.fib φ₀ φ₁ A α₀ α₁ eqFib) (ρ ×id)
    ≡ UnionIsFib.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (A ∘ ρ ×id)
      (reindex _ α₀ (ρ ×id)) (reindex _ α₁ (ρ ×id)) (cong (reindexFib ◆ (ρ ×id)) eqFib)
reindexUnion φ₀ φ₁ A α₀ α₁ eqFib ρ =
  unionIsFibExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (cong (reindex (A ∘ inl' φ₀ φ₁) ◆ (ρ ×id)) (UnionIsFib.left φ₀ φ₁ A α₀ α₁ eqFib)
      ∙ symm (UnionIsFib.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))
    (cong (reindex (A ∘ inr' φ₀ φ₁) ◆ (ρ ×id)) (UnionIsFib.right φ₀ φ₁ A α₀ α₁ eqFib)
      ∙ symm (UnionIsFib.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))

module FibUnion {ℓ ℓ'} {Γ : Set ℓ} (φ₀ φ₁ : Γ → CofProp)
  (Aα₀ : Fib ℓ' (Γ ,[ φ₀ ])) (Aα₁ : Fib ℓ' (Γ ,[ φ₁ ]))
  (eqFib : reindexFib Aα₀ (id× fst) ≡ reindexFib Aα₁ (id× snd))
  where

  private
    module F = UnionIsFib φ₀ φ₁
      (uncurry λ x →
        ∨-rec (φ₀ x) (φ₁ x)
          (curry (Aα₀ .fst) x)
          (curry (Aα₁ .fst) x)
          (λ u₀ u₁ → cong (λ Bβ → Bβ .fst (x , u₀ , u₁)) eqFib))
      (Aα₀ .snd)
      (Aα₁ .snd)
      eqFib

  opaque
    fib : Fib ℓ' (Γ ,[ φ₀ ∨' φ₁ ])
    fib = (_ , F.fib)

    left : reindexFib fib (inl' φ₀ φ₁) ≡ Aα₀
    left = cong (λ f → Aα₀ .fst , f) F.left

    right : reindexFib fib (inr' φ₀ φ₁) ≡ Aα₁
    right = cong (λ f → Aα₁ .fst , f) F.right

reindexFibUnion : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (Aα₀ : Fib ℓ'' (Γ ,[ φ₀ ])) (Aα₁ : Fib ℓ'' (Γ ,[ φ₁ ]))
  (eqFib : reindexFib Aα₀ (id× fst) ≡ reindexFib Aα₁ (id× snd))
  (ρ : Δ → Γ)
  → reindexFib (FibUnion.fib φ₀ φ₁ Aα₀ Aα₁ eqFib) (ρ ×id)
    ≡ FibUnion.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (reindexFib Aα₀ (ρ ×id)) (reindexFib Aα₁ (ρ ×id))
        (cong (reindexFib ◆ (ρ ×id)) eqFib)
reindexFibUnion {Δ = Δ} φ₀ φ₁ Aα₀ Aα₁ eqFib ρ =
  unionFibExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (cong (reindexFib ◆ (ρ ×id)) (FibUnion.left φ₀ φ₁ Aα₀ Aα₁ eqFib)
      ∙ symm (FibUnion.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
    (cong (reindexFib ◆ (ρ ×id)) (FibUnion.right φ₀ φ₁ Aα₀ Aα₁ eqFib)
      ∙ symm (FibUnion.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
