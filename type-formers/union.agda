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
  → α₀ ∘ᶠˢ (id× ∨l) ≡ α₁ ∘ᶠˢ (id× ∨l)
  → α₀ ∘ᶠˢ (id× ∨r) ≡ α₁ ∘ᶠˢ (id× ∨r)
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
      → β .lift S r p box .fill s .out ≡ move u eq (β ∘ᶠˢ (fst ∘ p ,, u))
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
                    (β ∘ᶠˢ (fst ∘ p ,, u₀)))
                eq₀
          ∙ sym (moveEq (∨l ∘ u₀) (funext λ _ → trunc _ _) α₁))
        (λ u₁ →
          moveEq (∨r ∘ u₁) (funext λ _ → trunc _ _) α₀
          ∙ cong
                (λ β →
                  move (∨r ∘ u₁) (funext λ _ → trunc _ _)
                    (β ∘ᶠˢ (fst ∘ p ,, u₁)))
                eq₁
          ∙ sym (moveEq (∨r ∘ u₁) (funext λ _ → trunc _ _) α₁))

unionFibExt : {Γ : Type ℓ} (φ₀ φ₁ : Γ → CofProp)
  {A₀ A₁ : Fib ℓ' (Γ ,[ φ₀ ∨ᴵ φ₁ ])}
  → A₀ ∘ᶠ (id× ∨l) ≡ A₁ ∘ᶠ (id× ∨l)
  → A₀ ∘ᶠ (id× ∨r) ≡ A₁ ∘ᶠ (id× ∨r)
  → A₀ ≡ A₁
unionFibExt φ₀ φ₁ {A₀} {A₁} eq₀ eq₁ =
  lemma
    (funext
      (uncurry λ x → ∨-elimEq (φ₀ x) (φ₁ x)
        (λ u₀ → appCong (cong fst eq₀))
        (λ u₁ → appCong (cong fst eq₁))))
  where
  lemma : A₀ .fst ≡ A₁ .fst → A₀ ≡ A₁
  lemma refl =
    cong (A₁ .fst ,_)
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
  (eqFib : (_ , α₀) ∘ᶠ wk[ φ₁ ∘ fst ] ≡ (_ , α₁) ∘ᶠ (wk[ φ₀ ] ×id))
  {u : ∀ s → [ φ₀ s ∨ φ₁ s ]}
  (box : OpenBox S r (A ∘ (id ,, u)))
  where

  fillSys : ∀ s → [ all S φ₀ ∨ all S φ₁ ] → A (s , u s) [ box .cof ↦ box .tube ◆ s ]
  fillSys s =
    ∨-rec (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (α₀ ∘ᶠˢ (id ,, u₀))
          .lift S r id box .fill s)
      (λ u₁ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (α₁ ∘ᶠˢ (id ,, u₁))
          .lift S r id box .fill s)
      (λ u₀ u₁ →
        congΣ
          (λ u' α' →
            subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc (u' s) _) α'
              .lift S r id box .fill s)
          (funext λ _ → trunc _ _)
          (substCongAssoc FibStr (λ u' → A ∘ (id ,, u')) (funext λ s → trunc _ _) _
            ∙ Σeq₂
                (cong (λ Aα' → Aα' ∘ᶠ ((id ,, u₀) ,, u₁)) eqFib)
                (cong (λ u' → A ∘ (id ,, u')) (funext λ _ → trunc _ _))))

  capSys : (u : [ all S φ₀ ∨ all S φ₁ ]) → fillSys r u .out ≡ box .cap .out
  capSys =
    ∨-elimEq (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (α₀ ∘ᶠˢ (id ,, u₀))
          .lift S r id box .cap≡)
      (λ u₁ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (α₁ ∘ᶠˢ (id ,, u₁))
          .lift S r id box .cap≡)

  filler : Filler box
  filler .fill s = fillSys s (shape→∨ S φ₀ φ₁ u)
  filler .cap≡ = capSys (shape→∨ S φ₀ φ₁ u)

module UnionVary {S T r} (σ : ShapeHom S T)
  (φ₀ φ₁ : ⟨ T ⟩ → CofProp)
  (A : ⟨ T ⟩ ,[ φ₀ ∨ᴵ φ₁ ] → Type ℓ)
  (α₀ : FibStr (A ∘ id× ∨l))
  (α₁ : FibStr (A ∘ id× ∨r))
  (eqFib : (_ , α₀) ∘ᶠ wk[ φ₁ ∘ fst ] ≡ (_ , α₁) ∘ᶠ (wk[ φ₀ ] ×id))
  {u : ∀ t → [ φ₀ t ∨ φ₁ t ]}
  (box : OpenBox T (⟪ σ ⟫ r) (λ t → A (t , u t)))
  where

  module T = UnionLift φ₀ φ₁ A α₀ α₁ eqFib box
  module S =
    UnionLift (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫)
      (A ∘ ⟪ σ ⟫ ×id)
      (α₀ ∘ᶠˢ (⟪ σ ⟫ ×id))
      (α₁ ∘ᶠˢ (⟪ σ ⟫ ×id))
      (cong (_∘ᶠ (⟪ σ ⟫ ×id ×id)) eqFib)
      (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    ∨-elimEq (all T φ₀) (all T φ₁)
      {f = λ u → T.fillSys (⟪ σ ⟫ s) u .out}
      {g = λ _ → S.fillSys s (shape→∨ S (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫) (u ∘ ⟪ σ ⟫)) .out}
      (λ u₀ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funext λ s → trunc _ _)
          (α₀ ∘ᶠˢ (id ,, u₀))
          .vary S T σ r id box s
        ∙
        cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
          (substNaturality
                (λ u' → FibStr (A ∘ (id ,, u')))
                (λ u' → FibStr (A ∘ (id ,, u') ∘ ⟪ σ ⟫))
                (λ u' α → α ∘ᶠˢ ⟪ σ ⟫)
                (funext λ t → trunc (∨l (u₀ t)) (u t))
                (α₀ ∘ᶠˢ (id ,, u₀))
           ∙
           substCongAssoc
             (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u')))
             (_∘ ⟪ σ ⟫)
             (funext λ t → trunc _ _)
             (α₀ ∘ᶠˢ ((id ,, u₀) ∘ ⟪ σ ⟫))
           ∙
           cong
             (λ eq →
                subst (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u'))) eq
                  (α₀ ∘ᶠˢ ((id ,, u₀) ∘ ⟪ σ ⟫)))
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
          (α₁ ∘ᶠˢ (id ,, u₁))
          .vary S T σ r id box s
        ∙
        cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
          (substNaturality
            (λ u' → FibStr (A ∘ (id ,, u')))
            (λ u' → FibStr (A ∘ (id ,, u') ∘ ⟪ σ ⟫))
            (λ u' α → α ∘ᶠˢ ⟪ σ ⟫)
            (funext λ t → trunc (∨r (u₁ t)) (u t))
            (α₁ ∘ᶠˢ (id ,, u₁))
           ∙
           substCongAssoc
             (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u')))
             (_∘ ⟪ σ ⟫)
             (funext λ t → trunc _ _)
             (α₁ ∘ᶠˢ ((id ,, u₁) ∘ ⟪ σ ⟫))
           ∙
           cong
             (λ eq →
               subst (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u'))) eq
                 (α₁ ∘ᶠˢ ((id ,, u₁) ∘ ⟪ σ ⟫)))
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
  (eqFib : (_ , α₀) ∘ᶠ wk[ φ₁ ∘ fst ] ≡ (_ , α₁) ∘ᶠ (wk[ φ₀ ] ×id))
  where

  opaque
    fib : FibStr A
    fib .lift S r p =
      UnionLift.filler
        (φ₀ ∘ fst ∘ p)
        (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (α₀ ∘ᶠˢ ((fst ∘ p) ×id))
        (α₁ ∘ᶠˢ ((fst ∘ p) ×id))
        (cong (_∘ᶠ ((fst ∘ p) ×id ×id)) eqFib)
    fib .vary S T σ r p =
      UnionVary.eq σ
        (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (α₀ ∘ᶠˢ ((fst ∘ p) ×id))
        (α₁ ∘ᶠˢ ((fst ∘ p) ×id))
        (cong (_∘ᶠ ((fst ∘ p) ×id ×id)) eqFib)

    -- TODO: prove the following in UnionLift

    left : fib ∘ᶠˢ (id× ∨l) ≡ α₀
    left = FibStrExt λ S r p box s →
      let
        open UnionLift (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (α₀ ∘ᶠˢ ((fst ∘ p) ×id))
          (α₁ ∘ᶠˢ ((fst ∘ p) ×id))
          (cong (_∘ᶠ ((fst ∘ p) ×id ×id)) eqFib)
          box
      in
      cong (out ∘ fillSys s)
        (trunc
          (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (∨l ∘ snd ∘ p))
          (∨l (snd ∘ p)))
      ∙
      cong
        (λ eq →
          subst (λ u' → FibStr (A ∘ (fst ∘ p ,, u'))) eq (α₀ ∘ᶠˢ p)
            .lift S r id box .fill s .out)
        (uip (funext λ _ → trunc _ _) refl)

    right : fib ∘ᶠˢ (id× ∨r) ≡ α₁
    right = FibStrExt λ S r p box s →
      let
        open UnionLift (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (α₀ ∘ᶠˢ ((fst ∘ p) ×id))
          (α₁ ∘ᶠˢ ((fst ∘ p) ×id))
          (cong (_∘ᶠ ((fst ∘ p) ×id ×id)) eqFib)
          box
      in
      cong (out ∘ fillSys s)
        (trunc
          (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (∨r ∘ snd ∘ p))
          (∨r (snd ∘ p)))
      ∙
      cong
        (λ eq →
          subst (λ u' → FibStr (A ∘ (fst ∘ p ,, u'))) eq (α₁ ∘ᶠˢ p)
            .lift S r id box .fill s .out)
        (uip (funext λ _ → trunc _ _) refl)

reindexUnionFibStr : {Δ : Type ℓ} {Γ : Type ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (A : Γ ,[ φ₀ ∨ᴵ φ₁ ] → Type ℓ'')
  (α₀ : FibStr (A ∘ id× ∨l))
  (α₁ : FibStr (A ∘ id× ∨r))
  (eqFib : (_ , α₀) ∘ᶠ wk[ φ₁ ∘ fst ] ≡ (_ , α₁) ∘ᶠ (wk[ φ₀ ] ×id))
  (ρ : Δ → Γ)
  → UnionFibStr.fib φ₀ φ₁ A α₀ α₁ eqFib ∘ᶠˢ (ρ ×id)
    ≡ UnionFibStr.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (A ∘ ρ ×id)
      (α₀ ∘ᶠˢ (ρ ×id))
      (α₁ ∘ᶠˢ (ρ ×id))
      (cong (_∘ᶠ (ρ ×id ×id)) eqFib)
reindexUnionFibStr φ₀ φ₁ A α₀ α₁ eqFib ρ =
  unionFibStrExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (cong (_∘ᶠˢ (ρ ×id)) (UnionFibStr.left φ₀ φ₁ A α₀ α₁ eqFib)
      ∙ sym (UnionFibStr.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))
    (cong (_∘ᶠˢ (ρ ×id)) (UnionFibStr.right φ₀ φ₁ A α₀ α₁ eqFib)
      ∙ sym (UnionFibStr.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _ _))

module Unionᶠ {Γ : Type ℓ} (φ₀ φ₁ : Γ → CofProp)
  (A₀ : Fib ℓ' (Γ ,[ φ₀ ])) (A₁ : Fib ℓ' (Γ ,[ φ₁ ]))
  (eqFib : A₀ ∘ᶠ wk[ φ₁ ∘ fst ] ≡ A₁ ∘ᶠ (wk[ φ₀ ] ×id))
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

  left : fib ∘ᶠ (id× ∨l) ≡ A₀
  left = cong (A₀ .fst ,_) F.left

  right : fib ∘ᶠ (id× ∨r) ≡ A₁
  right = cong (A₁ .fst ,_) F.right

reindexUnionᶠ : {Δ : Type ℓ} {Γ : Type ℓ'} (φ₀ φ₁ : Γ → CofProp)
  (A₀ : Fib ℓ'' (Γ ,[ φ₀ ])) (A₁ : Fib ℓ'' (Γ ,[ φ₁ ]))
  (eqFib : A₀ ∘ᶠ wk[ φ₁ ∘ fst ] ≡ A₁ ∘ᶠ (wk[ φ₀ ] ×id))
  (ρ : Δ → Γ)
  → (Unionᶠ.fib φ₀ φ₁ A₀ A₁ eqFib) ∘ᶠ (ρ ×id)
    ≡ Unionᶠ.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (A₀ ∘ᶠ (ρ ×id)) (A₁ ∘ᶠ (ρ ×id))
        (cong (_∘ᶠ (ρ ×id ×id)) eqFib)
reindexUnionᶠ {Δ = Δ} φ₀ φ₁ A₀ A₁ eqFib ρ =
  unionFibExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
    (cong (_∘ᶠ (ρ ×id)) (Unionᶠ.left φ₀ φ₁ A₀ A₁ eqFib)
      ∙ sym (Unionᶠ.left (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
    (cong (_∘ᶠ (ρ ×id)) (Unionᶠ.right φ₀ φ₁ A₀ A₁ eqFib)
      ∙ sym (Unionᶠ.right (φ₀ ∘ ρ) (φ₁ ∘ ρ) _ _ _))
