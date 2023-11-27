{-

Definitions of contractible, fibers, equivalences.

-}
{-# OPTIONS --rewriting --lossy-unification #-}
module type-formers.equivs where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.coercion
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma

private variable ℓ ℓ' ℓ'' ℓ''' : Level

------------------------------------------------------------------------------------------
-- Homotopy-contractibility
------------------------------------------------------------------------------------------

IsContr : Type ℓ → Type ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContrᴵ : {Γ : Type ℓ} → (Γ → Type ℓ') → (Γ → Type ℓ')
IsContrᴵ A x = IsContr (A x)

IsContrᶠ : {Γ : Type ℓ} → Γ ⊢ᶠType ℓ' → Γ ⊢ᶠType ℓ'
IsContrᶠ A = Σᶠ A (Πᶠ (A ∘ᶠ fst) (Pathᶠ (A ∘ᶠ fst ∘ᶠ fst) snd (snd ∘ fst)))

opaque
  reindexIsContrᶠ : {Δ : Type ℓ} {Γ : Type ℓ'}
    (A : Γ ⊢ᶠType ℓ'')
    (ρ : Δ → Γ)
    → IsContrᶠ A ∘ᶠ ρ ≡ IsContrᶠ (A ∘ᶠ ρ)
  reindexIsContrᶠ A ρ =
    reindexΣᶠ _ _ _ ∙ cong (Σᶠ _) (reindexΠᶠ _ _ _ ∙ cong (Πᶠ _) (reindexPathᶠ _ _))

------------------------------------------------------------------------------------------
-- Homotopy fiber type
------------------------------------------------------------------------------------------

Fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (b : B) → Type (ℓ ⊔ ℓ')
Fiber f b = Σ a ∈ _ , f a ~ b

Fiberᴵ : {Γ : Type ℓ} {A : Γ → Type ℓ'} {B : Γ → Type ℓ''}
  (f : Γ ⊢ A →ᴵ B)
  (b : Γ ⊢ B)
  → Γ → Type (ℓ' ⊔ ℓ'')
Fiberᴵ f b γ = Fiber (f γ) (b γ)

Fiberᶠ : {Γ : Type ℓ} (A : Γ ⊢ᶠType ℓ') (B : Γ ⊢ᶠType ℓ'')
  (f : Γ ⊢ A .fst →ᴵ B .fst)
  (b : Γ ⊢ B .fst)
  → Γ ⊢ᶠType (ℓ' ⊔ ℓ'')
Fiberᶠ A B f b = Σᶠ A (Pathᶠ (B ∘ᶠ fst) (uncurry f) (b ∘ fst))

opaque
  reindexFiberᶠ : {Δ : Type ℓ} {Γ : Type ℓ'}
    (A : Γ ⊢ᶠType ℓ'') (B : Γ ⊢ᶠType ℓ''') {f : Γ ⊢ A .fst →ᴵ B .fst} {b : Γ ⊢ B .fst}
    (ρ : Δ → Γ)
    → Fiberᶠ A B f b ∘ᶠ ρ ≡ Fiberᶠ (A ∘ᶠ ρ) (B ∘ᶠ ρ) (f ∘ ρ) (b ∘ ρ)
  reindexFiberᶠ A B ρ =
    reindexΣᶠ _ _ _ ∙ cong (Σᶠ _) (reindexPathᶠ _ _)

module _ {A : Type ℓ} {B : Type ℓ'} {f : A → B} where

  FiberExt : {b : B} {x y : Fiber f b}
    → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → x ≡ y
  FiberExt refl p = Σext refl (PathExt p)

  FiberExtDep : {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
    → x .fst ≡ y .fst
    → (∀ i → x .snd .at i ≡ y .snd .at i)
    → subst (Fiber f) p x ≡ y
  FiberExtDep refl = FiberExt

  eqToFiber : {b : B} (a : A) → f a ≡ b → Fiber f b
  eqToFiber a eq = (a , eqToPath eq)

  fiberPathEq : {b : B} {x y : Fiber f b}
    → x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
  fiberPathEq refl _ = refl

  fiberPathEqDep : {b b' : B} (p : b ≡ b')
    {x : Fiber f b} {y : Fiber f b'}
    → subst (Fiber f) p x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
  fiberPathEqDep refl refl _ = refl

  fiberDomEqDep : {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
    → subst (Fiber f) p x ≡ y → x .fst ≡ y .fst
  fiberDomEqDep refl refl = refl

------------------------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------------------------

IsEquiv : {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type (ℓ ⊔ ℓ')
IsEquiv f = ∀ b → IsContr (Fiber f b)

IsEquivᴵ : {Γ : Type ℓ} {A : Γ → Type ℓ'} {B : Γ → Type ℓ''}
  (f : Γ ⊢ A →ᴵ B)
  → Γ → Type (ℓ' ⊔ ℓ'')
IsEquivᴵ f = Πᴵ _ (IsContrᴵ (Fiberᴵ (f ∘ fst) snd))

IsEquivᶠ : {Γ : Type ℓ} (A : Γ ⊢ᶠType ℓ') (B : Γ ⊢ᶠType ℓ'')
  (f : Γ ⊢ A .fst →ᴵ B .fst)
  → Γ ⊢ᶠType (ℓ' ⊔ ℓ'')
IsEquivᶠ A B f = Πᶠ B (IsContrᶠ (Fiberᶠ (A ∘ᶠ fst) (B ∘ᶠ fst) (f ∘ fst) snd))

reindexIsEquivᶠ : {Δ : Type ℓ} {Γ : Type ℓ'}
  (A : Γ ⊢ᶠType ℓ'')
  (B : Γ ⊢ᶠType ℓ''')
  {f : Γ ⊢ A .fst →ᴵ B .fst}
  (ρ : Δ → Γ)
  → IsEquivᶠ A B f ∘ᶠ ρ ≡ IsEquivᶠ (A ∘ᶠ ρ) (B ∘ᶠ ρ) (f ∘ ρ)
reindexIsEquivᶠ A B {f = f} ρ =
  reindexΠᶠ _ _ _
  ∙ cong (Πᶠ _) (reindexIsContrᶠ _ _ ∙ cong IsContrᶠ (reindexFiberᶠ _ (B ∘ᶠ fst) _))

Equiv : (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')
Equiv A B = Σ (A → B) IsEquiv

Equivᴵ : {Γ : Type ℓ} (A : Γ → Type ℓ') (B : Γ → Type ℓ'') → (Γ → Type (ℓ' ⊔ ℓ''))
Equivᴵ A B = Σᴵ (A →ᴵ B) (IsEquivᴵ snd)

-- TODO rename?
equivFun : {Γ : Type ℓ} {A : Γ → Type ℓ'} {B : Γ → Type ℓ''}
  → Γ ⊢ Equivᴵ A B
  → Γ ⊢ A →ᴵ B
equivFun = fst ∘_

Equivᶠ : {Γ : Type ℓ} (A : Γ ⊢ᶠType ℓ') (B : Γ ⊢ᶠType ℓ'') → Γ ⊢ᶠType (ℓ' ⊔ ℓ'')
Equivᶠ A B = Σᶠ (Πᶠ A (B ∘ᶠ fst)) (IsEquivᶠ (A ∘ᶠ fst) (B ∘ᶠ fst) snd)

opaque
  reindexEquivᶠ : {Δ : Type ℓ} {Γ : Type ℓ'}
    (A : Γ ⊢ᶠType ℓ'')
    (B : Γ ⊢ᶠType ℓ''')
    (ρ : Δ → Γ)
    → Equivᶠ A B ∘ᶠ ρ ≡ Equivᶠ (A ∘ᶠ ρ) (B ∘ᶠ ρ)
  reindexEquivᶠ A B ρ =
    reindexΣᶠ _ _ _
    ∙ congΣ Σᶠ
      (reindexΠᶠ _ _ _)
      (substCongAssoc ((_⊢ᶠType _) ∘ Σ _) fst (reindexΠᶠ _ _ _) _
        ∙ substConst _ _ _
        ∙ reindexIsEquivᶠ (A ∘ᶠ fst) _ _)

------------------------------------------------------------------------------------------
-- Identity and coercion maps are equivalences
------------------------------------------------------------------------------------------

idEquiv : {A : Type ℓ} → FibStr (λ (_ : 𝟙) → A) → Equiv A A
idEquiv α .fst a = a
idEquiv α .snd a .fst = (a , refl~ a)
idEquiv {A = A} α .snd a .snd (a' , p) = h
  where
  qBox : (i : 𝕀) → OpenBox 𝕚 1 (λ _ → A)
  qBox i .cof = ∂ i
  qBox i .tube = OI-rec i (λ {refl → p .at}) (λ {refl _ → a})
  qBox i .cap .out = a
  qBox i .cap .out≡ = OI-elim i (λ {refl → p .at1}) (λ {refl → refl})

  q : (i : 𝕀) → Filler (qBox i)
  q i = α .lift 𝕚 1 (λ _ → _) (qBox i)

  h : (a' , p) ~ (a , refl~ a)
  h .at i .fst = q i .fill 0 .out
  h .at i .snd = path (λ j → q i .fill j .out) refl (q i .cap≡)
  h .at0 =
    FiberExt
      (sym (q 0 .fill 0 .out≡ (∨l refl)) ∙ p .at0)
      (λ j → sym (q 0 .fill j .out≡ (∨l refl)))
  h .at1 =
    FiberExt
      (sym (q 1 .fill 0 .out≡ (∨r refl)))
      (λ j → sym (q 1 .fill j .out≡ (∨r refl)))

idEquivᶠ : (A : 𝟙 ⊢ᶠType ℓ) → Equiv (A .fst tt) (A .fst tt)
idEquivᶠ (_ , α) = idEquiv α

opaque
  coerceEquiv : (S : Shape)
    (A : ⟨ S ⟩ ⊢ᶠType ℓ )
    (r s : ⟨ S ⟩) → Equiv (A .fst r) (A .fst s)
  coerceEquiv S A r s =
    coerce S r (Equivᶠ (A ∘ᶠ (λ _ → r)) A) (idEquivᶠ (A ∘ᶠ (λ _ → r))) s

  coerceEquivCap : (S : Shape)
    (A : ⟨ S ⟩ ⊢ᶠType ℓ)
    (r : ⟨ S ⟩) → coerceEquiv S A r r ≡ idEquivᶠ (A ∘ᶠ (λ _ → r))
  coerceEquivCap S A r =
    coerceCap S r
      (Equivᶠ (A ∘ᶠ (λ _ → r)) A)
      (idEquivᶠ (A ∘ᶠ (λ _ → r)))

  coerceEquivVary : ∀ {ℓ} {S T : Shape} (σ : ShapeHom S T)
    (A : ⟨ T ⟩ ⊢ᶠType ℓ)
    (r s : ⟨ S ⟩)
    → coerceEquiv T A (⟪ σ ⟫ r) (⟪ σ ⟫ s) ≡ coerceEquiv S (A ∘ᶠ ⟪ σ ⟫) r s
  coerceEquivVary {S = S} σ A r s =
    coerceVary σ r
      (Equivᶠ (A ∘ᶠ (λ _ → ⟪ σ ⟫ r)) A)
      (idEquivᶠ (A ∘ᶠ (λ _ → ⟪ σ ⟫ r)))
      s
    ∙
    cong
      (λ β → coerce S r (_ , β) (idEquivᶠ (A ∘ᶠ (λ _ → ⟪ σ ⟫ r))) s)
      (Σeq₂ (reindexEquivᶠ (A ∘ᶠ (λ _ → ⟪ σ ⟫ r)) A ⟪ σ ⟫) refl)
