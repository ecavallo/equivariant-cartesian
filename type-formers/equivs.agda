{-

Definitions of contractible, fibers, equivalences.

-}
{-# OPTIONS --rewriting #-}
module type-formers.equivs where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.coercion
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Homotopy-contractibility
------------------------------------------------------------------------------------------

IsContr : Type ℓ → Type ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContrᴵ : (Γ → Type ℓ) → (Γ → Type ℓ)
IsContrᴵ A x = IsContr (A x)

opaque
  IsContrFibStr : {A : Γ → Type ℓ} (α : FibStr A) → FibStr (IsContrᴵ A)
  IsContrFibStr α  =
    ΣFibStr α (ΠFibStr (α ∘ᶠˢ fst) (PathFibStr (α ∘ᶠˢ fst ∘ᶠˢ fst) snd (snd ∘ fst)))

  reindexIsContrFibStr : {A : Γ → Type ℓ} (α : FibStr A) (ρ : Δ → Γ)
    → IsContrFibStr α ∘ᶠˢ ρ ≡ IsContrFibStr (α ∘ᶠˢ ρ)
  reindexIsContrFibStr α ρ =
    reindexΣFibStr _ _ _
    ∙ cong (ΣFibStr _) (reindexΠFibStr _ _ _ ∙ cong (ΠFibStr _) (reindexPathFibStr _ _))

IsContrᶠ : Γ ⊢ᶠType ℓ → Γ ⊢ᶠType ℓ
IsContrᶠ A .fst = IsContrᴵ (A .fst)
IsContrᶠ A .snd = IsContrFibStr (A .snd)


------------------------------------------------------------------------------------------
-- Homotopy fiber type
------------------------------------------------------------------------------------------

Fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (b : B) → Type (ℓ ⊔ ℓ')
Fiber f b = Σ a ∈ _ , f a ~ b

Fiberᴵ : {A : Γ → Type ℓ} {B : Γ → Type ℓ'} (f : Γ ⊢ A →ᴵ B) (b : Γ ⊢ B)
  → (Γ → Type (ℓ ⊔ ℓ'))
Fiberᴵ f b γ = Fiber (f γ) (b γ)

opaque
  FiberFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    (f : Γ ⊢ A →ᴵ B) (b : Γ ⊢ B)
    → FibStr (Fiberᴵ f b)
  FiberFibStr α β f b =
    ΣFibStr α (PathFibStr (β ∘ᶠˢ fst) (uncurry f) (b ∘ fst))

  reindexFiberFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    {f : Γ ⊢ A →ᴵ B} {b : Γ ⊢ B}
    (ρ : Δ → Γ)
    → FiberFibStr α β f b ∘ᶠˢ ρ ≡ FiberFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ ρ) (f ∘ ρ) (b ∘ ρ)
  reindexFiberFibStr α β ρ =
    reindexΣFibStr _ _ _ ∙ cong (ΣFibStr _) (reindexPathFibStr _ _)

Fiberᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') (f : Γ ⊢ᶠ A →ᶠ B) (b : Γ ⊢ᶠ B)
  → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Fiberᶠ A B f b .fst = Fiberᴵ f b
Fiberᶠ A B f b .snd = FiberFibStr (A .snd) (B .snd) f b

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

IsEquivᴵ : {A : Γ → Type ℓ} {B : Γ → Type ℓ'} (f : Γ ⊢ A →ᴵ B)
  → Γ → Type (ℓ ⊔ ℓ')
IsEquivᴵ f = Πᴵ _ (IsContrᴵ (Fiberᴵ (f ∘ fst) snd))

opaque
  IsEquivFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    (f : Γ ⊢ A →ᴵ B) → FibStr (IsEquivᴵ f)
  IsEquivFibStr α β f =
    ΠFibStr β (IsContrFibStr (FiberFibStr (α ∘ᶠˢ fst) (β ∘ᶠˢ fst) (f ∘ fst) snd))

  reindexIsEquivFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    {f : Γ ⊢ A →ᴵ B}
    (ρ : Δ → Γ)
    → IsEquivFibStr α β f ∘ᶠˢ ρ ≡ IsEquivFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ ρ) (f ∘ ρ)
  reindexIsEquivFibStr α β ρ =
    reindexΠFibStr _ _ _
    ∙ cong (ΠFibStr _)
        (reindexIsContrFibStr _ _
          ∙ cong IsContrFibStr (reindexFiberFibStr _ (β ∘ᶠˢ fst) _))

IsEquivᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') (f : Γ ⊢ᶠ A →ᶠ B)
  → Γ ⊢ᶠType (ℓ ⊔ ℓ')
IsEquivᶠ A B f .fst = IsEquivᴵ f
IsEquivᶠ A B f .snd = IsEquivFibStr (A .snd) (B .snd) f

Equiv : (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')
Equiv A B = Σ (A → B) IsEquiv

Equivᴵ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
Equivᴵ A B = Σᴵ (A →ᴵ B) (IsEquivᴵ snd)

-- TODO rename?
equivFun : {A : Γ → Type ℓ} {B : Γ → Type ℓ'} → Γ ⊢ Equivᴵ A B → Γ ⊢ A →ᴵ B
equivFun = fst ∘_

opaque
  EquivFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    → FibStr (Equivᴵ A B)
  EquivFibStr α β =
    ΣFibStr (ΠFibStr α (β ∘ᶠˢ fst)) (IsEquivFibStr (α ∘ᶠˢ fst) (β ∘ᶠˢ fst) snd)

  reindexEquivFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    (ρ : Δ → Γ) → EquivFibStr α β ∘ᶠˢ ρ ≡ EquivFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ ρ)
  reindexEquivFibStr α β ρ =
    reindexΣFibStr _ _ _
    ∙ cong₂ (λ α β → ΣFibStr α β)
      (reindexΠFibStr _ _ _)
      (reindexIsEquivFibStr _ _ _)

Equivᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Equivᶠ A B .fst = Equivᴵ (A .fst) (B .fst)
Equivᶠ A B .snd = EquivFibStr (A .snd) (B .snd)

reindexEquivᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ')
  (ρ : Δ → Γ) → Equivᶠ A B ∘ᶠ ρ ≡ Equivᶠ (A ∘ᶠ ρ) (B ∘ᶠ ρ)
reindexEquivᶠ A B ρ = Σext refl (reindexEquivFibStr _ _ _)

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
  qBox i .tube j = OI-rec i (λ {refl → p .at j}) (λ {refl → a})
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

idEquivᶠ : (A : 𝟙 ⊢ᶠType ℓ) → Equivᶠ A A .fst tt
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
