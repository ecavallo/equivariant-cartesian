{-

Composition structures on the union of partially defined types (i.e., a system of types)

-}
{-# OPTIONS --rewriting #-}
module type-formers.union where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------------------------
-- Equality of fibration structures on a union of families
------------------------------------------------------------------------------------------

unionFibStrExt : {Γ : Type ℓ} (φ₀ φ₁ : Γ → CofProp)
  {A : Γ ,[ φ₀ ∨ᴵ φ₁ ] → Type ℓ'} {α₀ α₁ : FibStr A}
  → reindexFibStr α₀ (id× ∨l) ≡ reindexFibStr α₁ (id× ∨l)
  → reindexFibStr α₀ (id× ∨r) ≡ reindexFibStr α₁ (id× ∨r)
  → α₀ ≡ α₁
unionFibStrExt {Γ = Γ} φ₀ φ₁ {A} {α₀} {α₁} eq₀ eq₁ =
  FibStrExt λ S r p box s →
    lemma S r p box s (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
  where
  module _ (S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → Γ ,[ φ₀ ∨ᴵ φ₁ ])
    (box : OpenBox S r (A ∘ p)) (s : ⟨ S ⟩)
    where
    move : (u : [ all S ((φ₀ ∨ᴵ φ₁) ∘ fst ∘ p) ]) (eq : u ≡ snd ∘ p)
      (β : FibStr (A ∘ (fst ∘ p ,, u)))
      → A (p s)
    move _ refl β = β .lift S r id box .fill s .out

    moveEq : (u : [ all S ((φ₀ ∨ᴵ φ₁) ∘ fst ∘ p) ]) (eq : u ≡ snd ∘ p) (β : FibStr A)
      → β .lift S r p box .fill s .out ≡ move u eq (reindexFibStr β (fst ∘ p ,, u))
    moveEq _ refl β = refl

    lemma : [ all S (φ₀ ∘ fst ∘ p) ∨ all S (φ₁ ∘ fst ∘ p) ]
      → α₀ .lift S r p box .fill s .out ≡ α₁ .lift S r p box .fill s .out
    lemma =
      ∨-elimEq (all S (φ₀ ∘ fst ∘ p)) (all S (φ₁ ∘ fst ∘ p))
        (λ u₀ →
          moveEq (∨l ∘ u₀) (funext λ _ → trunc _ _) α₀
          ∙ cong
                (λ β →
                  move (∨l ∘ u₀) (funext λ _ → trunc _ _)
                    (reindexFibStr β (fst ∘ p ,, u₀)))
                eq₀
          ∙ sym (moveEq (∨l ∘ u₀) (funext λ _ → trunc _ _) α₁))
        (λ u₁ →
          moveEq (∨r ∘ u₁) (funext λ _ → trunc _ _) α₀
          ∙ cong
                (λ β →
                  move (∨r ∘ u₁) (funext λ _ → trunc _ _)
                    (reindexFibStr β (fst ∘ p ,, u₁)))
                eq₁
          ∙ sym (moveEq (∨r ∘ u₁) (funext λ _ → trunc _ _) α₁))

unionFibExt : {Γ : Type ℓ} (φ₀ φ₁ : Γ → CofProp)
  {Aα₀ Aα₁ : Fib ℓ' (Γ ,[ φ₀ ∨ᴵ φ₁ ])}
  → reindexFib Aα₀ (id× ∨l) ≡ reindexFib Aα₁ (id× ∨l)
  → reindexFib Aα₀ (id× ∨r) ≡ reindexFib Aα₁ (id× ∨r)
  → Aα₀ ≡ Aα₁
unionFibExt φ₀ φ₁ {Aα₀} {Aα₁} eq₀ eq₁ =
  lemma
    (funext
      (uncurry λ x → ∨-elimEq (φ₀ x) (φ₁ x)
        (λ u₀ → cong (λ Bβ → Bβ .fst (x , u₀)) eq₀)
        (λ u₁ → cong (λ Bβ → Bβ .fst (x , u₁)) eq₁)))
  where
  lemma : Aα₀ .fst ≡ Aα₁ .fst → Aα₀ ≡ Aα₁
  lemma refl =
    cong (Aα₁ .fst ,_)
      (unionFibStrExt φ₀ φ₁
        (Σeq₂ eq₀ refl)
        (Σeq₂ eq₁ refl))

------------------------------------------------------------------------------------------
-- Deriving a fibrancy structure on a union
------------------------------------------------------------------------------------------

module UnionLift {S r} (φ₀ φ₁ : ⟨ S ⟩ → CofProp)
  (A : ⟨ S ⟩ ,[ φ₀ ∨ᴵ φ₁ ] → Type ℓ)
  (α₀ : FibStr (A ∘ id× ∨l))
  (α₁ : FibStr (A ∘ id× ∨r))
  (eqFib : reindexFib (_ , α₀) wk[ φ₁ ∘ fst ] ≡ reindexFib (_ , α₁) (wk[ φ₀ ] ×id))
  {u : ∀ s → [ φ₀ s ∨ φ₁ s ]}
  (box : OpenBox S r (A ∘ (id ,, u)))
  where

  fillSys : ∀ s → [ all S φ₀ ∨ all S φ₁ ] → A (s , u s) [ box .cof ↦ box .tube ◆ s ]
  fillSys s =
    ∨-rec (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (reindexFibStr α₀ (id ,, u₀))
          .lift S r id box .fill s)
      (λ u₁ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (reindexFibStr α₁ (id ,, u₁))
          .lift S r id box .fill s)
      (λ u₀ u₁ →
        congΣ
          (λ u' α' →
            subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc (u' s) _) α'
              .lift S r id box .fill s)
          (funext λ _ → trunc _ _)
          (substCongAssoc FibStr (λ u' → A ∘ (id ,, u')) (funext λ s → trunc _ _) _
            ∙ Σeq₂
                (cong (λ Aα' → reindexFib Aα' ((id ,, u₀) ,, u₁)) eqFib)
                (cong (λ u' → A ∘ (id ,, u')) (funext λ _ → trunc _ _))))

  capSys : (u : [ all S φ₀ ∨ all S φ₁ ]) → fillSys r u .out ≡ box .cap .out
  capSys =
    ∨-elimEq (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (reindexFibStr α₀ (id ,, u₀))
          .lift S r id box .cap≡)
      (λ u₁ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (reindexFibStr α₁ (id ,, u₁))
          .lift S r id box .cap≡)

  filler : Filler box
  filler .fill s = fillSys s (shape→∨ S φ₀ φ₁ u)
  filler .cap≡ = capSys (shape→∨ S φ₀ φ₁ u)

module UnionVary {S T r} (σ : ShapeHom S T)
  (φ₀ φ₁ : ⟨ T ⟩ → CofProp)
  (A : ⟨ T ⟩ ,[ φ₀ ∨ᴵ φ₁ ] → Type ℓ)
  (α₀ : FibStr (A ∘ id× ∨l))
  (α₁ : FibStr (A ∘ id× ∨r))
  (eqFib : reindexFib (_ , α₀) wk[ φ₁ ∘ fst ] ≡ reindexFib (_ , α₁) (wk[ φ₀ ] ×id))
  {u : ∀ t → [ φ₀ t ∨ φ₁ t ]}
  (box : OpenBox T (⟪ σ ⟫ r) (λ t → A (t , u t)))
  where

  module T = UnionLift φ₀ φ₁ A α₀ α₁ eqFib box
  module S =
    UnionLift (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫)
      (A ∘ ⟪ σ ⟫ ×id)
      (reindexFibStr α₀ (⟪ σ ⟫ ×id))
      (reindexFibStr α₁ (⟪ σ ⟫ ×id))
      (cong (reindexFib ◆ (⟪ σ ⟫ ×id ×id)) eqFib)
      (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    ∨-elimEq (all T φ₀) (all T φ₁)
      {f = λ u → T.fillSys (⟪ σ ⟫ s) u .out}
      {g = λ _ → S.fillSys s (shape→∨ S (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫) (u ∘ ⟪ σ ⟫)) .out}
      (λ u₀ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (reindexFibStr α₀ (id ,, u₀))
          .vary S T σ r id box s
        ∙
        cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
          (substNaturality
                (λ u' → FibStr (A ∘ (id ,, u')))
                (λ u' → FibStr (A ∘ (id ,, u') ∘ ⟪ σ ⟫))
                (λ u' α → reindexFibStr α ⟪ σ ⟫)
                (funext λ t → trunc (∨l (u₀ t)) (u t))
                (reindexFibStr α₀ (id ,, u₀))
           ∙
           substCongAssoc
             (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u')))
             (_∘ ⟪ σ ⟫)
             (funext λ t → trunc _ _)
             (reindexFibStr α₀ ((id ,, u₀) ∘ ⟪ σ ⟫))
           ∙
           cong
             (λ eq →
                subst (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u'))) eq
                  (reindexFibStr α₀ ((id ,, u₀) ∘ ⟪ σ ⟫)))
             (uip
               (cong (_∘ ⟪ σ ⟫) (funext λ t → trunc _ (u t)))
               (funext λ s → trunc _ (u (⟪ σ ⟫ s)))))
        ∙
        cong (λ u' → S.fillSys s u' .out)
          (trunc
            (∨l (u₀ ∘ ⟪ σ ⟫))
            (shape→∨ S (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫) (u ∘ ⟪ σ ⟫))))
      (λ u₁ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (reindexFibStr α₁ (id ,, u₁))
          .vary S T σ r id box s
        ∙
        cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
          (substNaturality
            (λ u' → FibStr (A ∘ (id ,, u')))
            (λ u' → FibStr (A ∘ (id ,, u') ∘ ⟪ σ ⟫))
            (λ u' α → reindexFibStr α ⟪ σ ⟫)
            (funext λ t → trunc (∨r (u₁ t)) (u t))
            (reindexFibStr α₁ (id ,, u₁))
           ∙
           substCongAssoc
             (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u')))
             (_∘ ⟪ σ ⟫)
             (funext λ t → trunc _ _)
             (reindexFibStr α₁ ((id ,, u₁) ∘ ⟪ σ ⟫))
           ∙
           cong
             (λ eq →
               subst (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u'))) eq
                 (reindexFibStr α₁ ((id ,, u₁) ∘ ⟪ σ ⟫)))
             (uip
               (cong (_∘ ⟪ σ ⟫) (funext λ t → trunc _ (u t)))
                 (funext λ s → trunc _ (u (⟪ σ ⟫ s)))))
        ∙
        cong (λ u' → S.fillSys s u' .out)
          (trunc
            (∨r (u₁ ∘ ⟪ σ ⟫))
            (shape→∨ S (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫) (u ∘ ⟪ σ ⟫))))
      (shape→∨ T φ₀ φ₁ u)


module UnionFibStr {Γ : Type ℓ} (φ₀ φ₁ : Γ → CofProp)
  (A : Γ ,[ φ₀ ∨ᴵ φ₁ ] → Type ℓ')
  (α₀ : FibStr (A ∘ id× ∨l))
  (α₁ : FibStr (A ∘ id× ∨r))
  (eqFib : reindexFib (_ , α₀) wk[ φ₁ ∘ fst ] ≡ reindexFib (_ , α₁) (wk[ φ₀ ] ×id))
  where

  opaque
    fib : FibStr A
    fib .lift S r p =
      UnionLift.filler
        (φ₀ ∘ fst ∘ p)
        (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (reindexFibStr α₀ ((fst ∘ p) ×id))
        (reindexFibStr α₁ ((fst ∘ p) ×id))
        (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id ×id)) eqFib)
    fib .vary S T σ r p =
      UnionVary.eq σ
        (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (reindexFibStr α₀ ((fst ∘ p) ×id))
        (reindexFibStr α₁ ((fst ∘ p) ×id))
        (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id ×id)) eqFib)

    -- TODO: prove the following in UnionLift

    left : reindexFibStr fib (id× ∨l) ≡ α₀
    left = FibStrExt λ S r p box s →
      let
        open UnionLift (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (reindexFibStr α₀ ((fst ∘ p) ×id))
          (reindexFibStr α₁ ((fst ∘ p) ×id))
          (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id ×id)) eqFib)
          box
      in
      cong (out ∘ fillSys s)
        (trunc
          (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (∨l ∘ snd ∘ p))
          (∨l (snd ∘ p)))
      ∙
      cong
        (λ eq →
          subst (λ u' → FibStr (A ∘ (fst ∘ p ,, u'))) eq (reindexFibStr α₀ p)
            .lift S r id box .fill s .out)
        (uip (funext λ _ → trunc _ _) refl)

    right : reindexFibStr fib (id× ∨r) ≡ α₁
    right = FibStrExt λ S r p box s →
      let
        open UnionLift (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (reindexFibStr α₀ ((fst ∘ p) ×id))
          (reindexFibStr α₁ ((fst ∘ p) ×id))
          (cong (λ Aα → reindexFib Aα ((fst ∘ p) ×id ×id)) eqFib)
          box
      in
      cong (out ∘ fillSys s)
        (trunc
          (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (∨r ∘ snd ∘ p))
          (∨r (snd ∘ p)))
      ∙
      cong
        (λ eq →
          subst (λ u' → FibStr (A ∘ (fst ∘ p ,, u'))) eq (reindexFibStr α₁ p)
            .lift S r id box .fill s .out)
        (uip (funext λ _ → trunc _ _) refl)

reindexUnionFibStr : {Δ : Type ℓ} {Γ : Type ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (A : Γ ,[ φ₀ ∨ᴵ φ₁ ] → Type ℓ'')
  (α₀ : FibStr (A ∘ id× ∨l))
  (α₁ : FibStr (A ∘ id× ∨r))
  (eqFib : reindexFib (_ , α₀) wk[ φ₁ ∘ fst ] ≡ reindexFib (_ , α₁) (wk[ φ₀ ] ×id))
  (ρ : Δ → Γ)
  → reindexFibStr (UnionFibStr.fib φ₀ φ₁ A α₀ α₁ eqFib) (ρ ×id)
    ≡ UnionFibStr.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (A ∘ ρ ×id)
      (reindexFibStr α₀ (ρ ×id))
      (reindexFibStr α₁ (ρ ×id))
      (cong (reindexFib ◆ (ρ ×id ×id)) eqFib)
reindexUnionFibStr φ₀ φ₁ A α₀ α₁ eqFib ρ =
  unionFibStrExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (cong (reindexFibStr ◆ (ρ ×id)) (UnionFibStr.left φ₀ φ₁ A α₀ α₁ eqFib)
      ∙ sym (UnionFibStr.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))
    (cong (reindexFibStr ◆ (ρ ×id)) (UnionFibStr.right φ₀ φ₁ A α₀ α₁ eqFib)
      ∙ sym (UnionFibStr.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))

module UnionFib {Γ : Type ℓ} (φ₀ φ₁ : Γ → CofProp)
  (A₀ : Fib ℓ' (Γ ,[ φ₀ ])) (A₁ : Fib ℓ' (Γ ,[ φ₁ ]))
  (eqFib : reindexFib A₀ wk[ φ₁ ∘ fst ] ≡ reindexFib A₁ (wk[ φ₀ ] ×id))
  where

  -- TODO expose these in a better way
  module F = UnionFibStr φ₀ φ₁
    (uncurry λ x →
      ∨-rec (φ₀ x) (φ₁ x)
        (curry (A₀ .fst) x)
        (curry (A₁ .fst) x)
        (λ u₀ u₁ → cong (λ B → B .fst ((x , u₀) , u₁)) eqFib))
    (A₀ .snd)
    (A₁ .snd)
    eqFib

  fib : Fib ℓ' (Γ ,[ φ₀ ∨ᴵ φ₁ ])
  fib = (_ , F.fib)

  left : reindexFib fib (id× ∨l) ≡ A₀
  left = cong (A₀ .fst ,_) F.left

  right : reindexFib fib (id× ∨r) ≡ A₁
  right = cong (A₁ .fst ,_) F.right

reindexFibUnion : {Δ : Type ℓ} {Γ : Type ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (A₀ : Fib ℓ'' (Γ ,[ φ₀ ])) (A₁ : Fib ℓ'' (Γ ,[ φ₁ ]))
  (eqFib : reindexFib A₀ wk[ φ₁ ∘ fst ] ≡ reindexFib A₁ (wk[ φ₀ ] ×id))
  (ρ : Δ → Γ)
  → reindexFib (UnionFib.fib φ₀ φ₁ A₀ A₁ eqFib) (ρ ×id)
    ≡ UnionFib.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (reindexFib A₀ (ρ ×id)) (reindexFib A₁ (ρ ×id))
        (cong (reindexFib ◆ (ρ ×id ×id)) eqFib)
reindexFibUnion {Δ = Δ} φ₀ φ₁ A₀ A₁ eqFib ρ =
  unionFibExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (cong (reindexFib ◆ (ρ ×id)) (UnionFib.left φ₀ φ₁ A₀ A₁ eqFib)
      ∙ sym (UnionFib.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
    (cong (reindexFib ◆ (ρ ×id)) (UnionFib.right φ₀ φ₁ A₀ A₁ eqFib)
      ∙ sym (UnionFib.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
