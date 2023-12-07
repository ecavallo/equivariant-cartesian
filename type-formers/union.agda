{-

Composition structures on the union of partially defined types (i.e., a system of types)

-}
module type-formers.union where

open import prelude
open import axioms
open import fibration.fibration

private variable
  ℓ : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Equality of fibration structures on a union of families
------------------------------------------------------------------------------------------

unionFibStrExt : (φ₀ φ₁ : Γ → Cof)
  {A : Γ ▷[ φ₀ ∨ᴵ φ₁ ] → Type ℓ} {α₀ α₁ : FibStr A}
  → α₀ ∘ᶠˢ id× ∨l ≡ α₁ ∘ᶠˢ id× ∨l
  → α₀ ∘ᶠˢ id× ∨r ≡ α₁ ∘ᶠˢ id× ∨r
  → α₀ ≡ α₁
unionFibStrExt φ₀ φ₁ {A} {α₀} {α₁} eq₀ eq₁ =
  FibStrExt λ S r p box s →
    lemma S r p box s (shape→∨ S (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p) (snd ∘ p))
  where
  module _ (S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → _ ▷[ φ₀ ∨ᴵ φ₁ ])
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
          moveEq (∨l ∘ u₀) (funExt' trunc') α₀
          ∙ cong (λ β → move (∨l ∘ u₀) (funExt' trunc') (β ∘ᶠˢ (fst ∘ p ,, u₀))) eq₀
          ∙ sym (moveEq (∨l ∘ u₀) (funExt' trunc') α₁))
        (λ u₁ →
          moveEq (∨r ∘ u₁) (funExt' trunc') α₀
          ∙ cong (λ β → move (∨r ∘ u₁) (funExt' trunc') (β ∘ᶠˢ (fst ∘ p ,, u₁))) eq₁
          ∙ sym (moveEq (∨r ∘ u₁) (funExt' trunc') α₁))

unionFibExt : (φ₀ φ₁ : Γ → Cof)
  {A₀ A₁ : Γ ▷[ φ₀ ∨ᴵ φ₁ ] ⊢ᶠType ℓ}
  → A₀ ∘ᶠ id× ∨l ≡ A₁ ∘ᶠ id× ∨l
  → A₀ ∘ᶠ id× ∨r ≡ A₁ ∘ᶠ id× ∨r
  → A₀ ≡ A₁
unionFibExt φ₀ φ₁ {A₀} {A₁} eq₀ eq₁ =
  lemma
    (funExt
      (uncurry λ x → ∨-elimEq (φ₀ x) (φ₁ x)
        (λ u₀ → appCong $ cong fst eq₀)
        (λ u₁ → appCong $ cong fst eq₁)))
  where
  lemma : A₀ .fst ≡ A₁ .fst → A₀ ≡ A₁
  lemma refl =
    cong (A₁ .fst ,_) (unionFibStrExt φ₀ φ₁ (Σeq₂ eq₀ refl) (Σeq₂ eq₁ refl))

------------------------------------------------------------------------------------------
-- Deriving a fibrancy structure on a union
------------------------------------------------------------------------------------------

module UnionLift {S r} (φ₀ φ₁ : ⟨ S ⟩ → Cof)
  (A : ⟨ S ⟩ ▷[ φ₀ ∨ᴵ φ₁ ] → Type ℓ)
  (α₀ : FibStr (A ∘ id× ∨l))
  (α₁ : FibStr (A ∘ id× ∨r))
  (eqFib : (_ , α₀) ∘ᶠ wk[ φ₁ ∘ fst ] ≡ (_ , α₁) ∘ᶠ (wk[ φ₀ ] ×id))
  {u : ∀ s → [ φ₀ s ∨ φ₁ s ]}
  (box : OpenBox S r (A ∘ (id ,, u)))
  where

  fillSys : ∀ s → [ all S φ₀ ∨ all S φ₁ ] → A (s , u s) [ box .cof ↦ box .tube s ]
  fillSys s =
    ∨-rec (all S φ₀) (all S φ₁)
      (λ u₀ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funExt' trunc') (α₀ ∘ᶠˢ (id ,, u₀))
          .lift S r id box .fill s)
      (λ u₁ →
        subst (λ u' → FibStr (A ∘ (id ,, u'))) (funExt' trunc') (α₁ ∘ᶠˢ (id ,, u₁))
          .lift S r id box .fill s)
      (λ u₀ u₁ →
        congΣ
          (λ u' α' →
            subst (λ u' → FibStr (A ∘ (id ,, u'))) (funExt' trunc') α'
              .lift S r id box .fill s)
          (funExt' trunc')
          (substCongAssoc FibStr (λ u' → A ∘ (id ,, u')) (funExt' trunc') _
            ∙ Σeq₂
                (cong (_∘ᶠ ((id ,, u₀) ,, u₁)) eqFib)
                (cong (λ u' → A ∘ (id ,, u')) (funExt' trunc'))))

  opaque
    capSys : (u : [ all S φ₀ ∨ all S φ₁ ]) → fillSys r u .out ≡ box .cap .out
    capSys =
      ∨-elimEq (all S φ₀) (all S φ₁)
        (λ u₀ →
          subst (λ u' → FibStr (A ∘ (id ,, u'))) (funExt' trunc') (α₀ ∘ᶠˢ (id ,, u₀))
            .lift S r id box .cap≡)
        (λ u₁ →
          subst (λ u' → FibStr (A ∘ (id ,, u'))) (funExt' trunc') (α₁ ∘ᶠˢ (id ,, u₁))
            .lift S r id box .cap≡)

  filler : Filler box
  filler .fill s = fillSys s (shape→∨ S φ₀ φ₁ u)
  filler .cap≡ = capSys (shape→∨ S φ₀ φ₁ u)

module UnionVary {S T r} (σ : ShapeHom S T)
  (φ₀ φ₁ : ⟨ T ⟩ → Cof)
  (A : ⟨ T ⟩ ▷[ φ₀ ∨ᴵ φ₁ ] → Type ℓ)
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
      (α₀ ∘ᶠˢ ⟪ σ ⟫ ×id)
      (α₁ ∘ᶠˢ ⟪ σ ⟫ ×id)
      (cong (_∘ᶠ ⟪ σ ⟫ ×id ×id) eqFib)
      (reshapeBox σ box)

  opaque
    eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
    eq s =
      ∨-elimEq (all T φ₀) (all T φ₁)
        {f = λ u → T.fillSys (⟪ σ ⟫ s) u .out}
        {g = λ _ → S.fillSys s (shape→∨ S (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫) (u ∘ ⟪ σ ⟫)) .out}
        (λ u₀ →
          subst (λ u' → FibStr (A ∘ (id ,, u'))) (funExt' trunc') (α₀ ∘ᶠˢ (id ,, u₀))
            .vary S T σ r id box s
          ∙
          cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
            (substNaturality (λ u' α → α ∘ᶠˢ ⟪ σ ⟫) _
             ∙
             substCongAssoc
               (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u')))
               (_∘ ⟪ σ ⟫)
               (funExt' trunc')
               (α₀ ∘ᶠˢ (id ,, u₀) ∘ᶠˢ ⟪ σ ⟫)
             ∙
             cong
               (subst (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u'))) ⦅–⦆ (α₀ ∘ᶠˢ (id ,, u₀) ∘ᶠˢ ⟪ σ ⟫))
               (uip (cong (_∘ ⟪ σ ⟫) $ funExt' trunc') (funExt' trunc')))
          ∙
          cong (λ u' → S.fillSys s u' .out)
            (trunc
              (∨l (u₀ ∘ ⟪ σ ⟫))
              (shape→∨ S (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫) (u ∘ ⟪ σ ⟫))))
        (λ u₁ →
          subst (λ u' → FibStr (A ∘ (id ,, u'))) (funExt' trunc') (α₁ ∘ᶠˢ (id ,, u₁))
            .vary S T σ r id box s
          ∙
          cong (λ α → α .lift S r id (reshapeBox σ box) .fill s .out)
            (substNaturality (λ u' α → α ∘ᶠˢ ⟪ σ ⟫) _
             ∙
             substCongAssoc
               (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u')))
               (_∘ ⟪ σ ⟫)
               (funExt' trunc')
               (α₁ ∘ᶠˢ (id ,, u₁) ∘ᶠˢ ⟪ σ ⟫)
             ∙
             cong
               (subst (λ u' → FibStr (A ∘ (⟪ σ ⟫ ,, u'))) ⦅–⦆ (α₁ ∘ᶠˢ (id ,, u₁) ∘ᶠˢ ⟪ σ ⟫))
               (uip (cong (_∘ ⟪ σ ⟫) $ funExt' trunc') (funExt' trunc')))
          ∙
          cong (λ u' → S.fillSys s u' .out)
            (trunc
              (∨r (u₁ ∘ ⟪ σ ⟫))
              (shape→∨ S (φ₀ ∘ ⟪ σ ⟫) (φ₁ ∘ ⟪ σ ⟫) (u ∘ ⟪ σ ⟫))))
        (shape→∨ T φ₀ φ₁ u)


module UnionFibStr (φ₀ φ₁ : Γ → Cof)
  (A : Γ ▷[ φ₀ ∨ᴵ φ₁ ] → Type ℓ)
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
        (α₀ ∘ᶠˢ (fst ∘ p) ×id)
        (α₁ ∘ᶠˢ (fst ∘ p) ×id)
        (cong (_∘ᶠ (fst ∘ p) ×id ×id) eqFib)
    fib .vary S T σ r p =
      UnionVary.eq σ
        (φ₀ ∘ fst ∘ p)  (φ₁ ∘ fst ∘ p)
        (A ∘ (fst ∘ p) ×id)
        (α₀ ∘ᶠˢ (fst ∘ p) ×id)
        (α₁ ∘ᶠˢ (fst ∘ p) ×id)
        (cong (_∘ᶠ (fst ∘ p) ×id ×id) eqFib)

    -- TODO: prove the following in UnionLift

    left : fib ∘ᶠˢ (id× ∨l) ≡ α₀
    left = FibStrExt λ S r p box s →
      let
        open UnionLift (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (α₀ ∘ᶠˢ (fst ∘ p) ×id)
          (α₁ ∘ᶠˢ (fst ∘ p) ×id)
          (cong (_∘ᶠ (fst ∘ p) ×id ×id) eqFib)
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
        (uip (funExt' trunc') refl)

    right : fib ∘ᶠˢ (id× ∨r) ≡ α₁
    right = FibStrExt λ S r p box s →
      let
        open UnionLift (φ₀ ∘ fst ∘ p) (φ₁ ∘ fst ∘ p)
          (A ∘ (fst ∘ p) ×id)
          (α₀ ∘ᶠˢ (fst ∘ p) ×id)
          (α₁ ∘ᶠˢ (fst ∘ p) ×id)
          (cong (_∘ᶠ (fst ∘ p) ×id ×id) eqFib)
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
        (uip (funExt' trunc') refl)

module Unionᶠ (φ₀ φ₁ : Γ → Cof)
  (A₀ : Γ ▷[ φ₀ ] ⊢ᶠType ℓ) (A₁ : Γ ▷[ φ₁ ] ⊢ᶠType ℓ)
  (eqFib : A₀ ∘ᶠ wk[ φ₁ ∘ fst ] ≡ A₁ ∘ᶠ wk[ φ₀ ] ×id)
  where

  private
    Ty : Γ ▷[ φ₀ ∨ᴵ φ₁ ] → Type ℓ
    Ty = uncurry λ γ →
      ∨-rec (φ₀ γ) (φ₁ γ)
        (curry (A₀ .fst) γ)
        (curry (A₁ .fst) γ)
        (λ u₀ u₁ → cong (λ B → B .fst (γ , u₀ , u₁)) eqFib)

  -- TODO expose these in a better way
  module F = UnionFibStr φ₀ φ₁ Ty (A₀ .snd) (A₁ .snd) eqFib

  fib : Γ ▷[ φ₀ ∨ᴵ φ₁ ] ⊢ᶠType ℓ
  fib .fst = Ty
  fib .snd = F.fib

  opaque
    left : fib ∘ᶠ (id× ∨l) ≡ A₀
    left = cong (A₀ .fst ,_) F.left

    right : fib ∘ᶠ (id× ∨r) ≡ A₁
    right = cong (A₁ .fst ,_) F.right

opaque
  reindexUnionᶠ : {φ₀ φ₁ : Γ → Cof}
    {A₀ : Γ ▷[ φ₀ ] ⊢ᶠType ℓ} {A₁ : Γ ▷[ φ₁ ] ⊢ᶠType ℓ}
    {eqFib : A₀ ∘ᶠ wk[ φ₁ ∘ fst ] ≡ A₁ ∘ᶠ wk[ φ₀ ] ×id}
    (ρ : Δ → Γ)
    → (Unionᶠ.fib φ₀ φ₁ A₀ A₁ eqFib) ∘ᶠ ρ ×id
      ≡ Unionᶠ.fib (φ₀ ∘ ρ) (φ₁ ∘ ρ) (A₀ ∘ᶠ ρ ×id) (A₁ ∘ᶠ ρ ×id)
          (cong (_∘ᶠ ρ ×id ×id) eqFib)
  reindexUnionᶠ {φ₀ = φ₀} {φ₁ = φ₁} ρ =
    unionFibExt (φ₀ ∘ ρ) (φ₁ ∘ ρ)
      (cong (_∘ᶠ ρ ×id) (Unionᶠ.left _ _ _ _ _) ∙ sym (Unionᶠ.left _ _ _ _ _))
      (cong (_∘ᶠ ρ ×id) (Unionᶠ.right _ _ _ _ _) ∙ sym (Unionᶠ.right _ _ _ _ _))
