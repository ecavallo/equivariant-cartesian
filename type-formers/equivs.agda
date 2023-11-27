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

private variable ℓ ℓ' ℓ'' ℓ''' : Level

------------------------------------------------------------------------------------------
-- Homotopy-contractibility
------------------------------------------------------------------------------------------

IsContr : Type ℓ → Type ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContrᴵ : {Γ : Type ℓ} → (Γ → Type ℓ') → (Γ → Type ℓ')
IsContrᴵ A x = IsContr (A x)

opaque
  IsContrFibStr : {Γ : Type ℓ} {A : Γ → Type ℓ'}
    → FibStr A → FibStr (IsContrᴵ A)
  IsContrFibStr α =
    ΣFibStr
      α
      (ΠFibStr
        (reindexFibStr α fst)
        (PathFibStr (reindexFibStr α (fst ∘ fst)) snd (snd ∘ fst)))

  reindexIsContrFibStr : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A : Γ → Type ℓ''}
    (α : FibStr A)
    (ρ : Δ → Γ)
    → reindexFibStr (IsContrFibStr α) ρ ≡ IsContrFibStr (reindexFibStr α ρ)
  reindexIsContrFibStr α ρ =
    reindexΣFibStr _ _ _
    ∙ cong (ΣFibStr _) (reindexΠFibStr _ _ _ ∙ cong (ΠFibStr _) (reindexPath _ _))

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

opaque
  FiberFibStr : {Γ : Type ℓ}
    {A : Γ → Type ℓ'} (α : FibStr A)
    {B : Γ → Type ℓ''} (b : FibStr B)
    (f : Γ ⊢ A →ᴵ B)
    (b : Γ ⊢ B)
    → FibStr (Fiberᴵ f b)
  FiberFibStr α β f b =
    ΣFibStr α (PathFibStr (reindexFibStr β fst) _ _)

  reindexFiberFibStr : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A : Γ → Type ℓ''} (α : FibStr A)
    {B : Γ → Type ℓ'''} (β : FibStr B)
    {f : Γ ⊢ A →ᴵ B}
    {b : Γ ⊢ B}
    (ρ : Δ → Γ)
    → reindexFibStr (FiberFibStr α β f b) ρ
      ≡ FiberFibStr (reindexFibStr α ρ) (reindexFibStr β ρ) (f ∘ ρ) (b ∘ ρ)
  reindexFiberFibStr α β ρ =
    reindexΣFibStr _ _ _ ∙ cong (ΣFibStr _) (reindexPath _ _)

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

IsEquivFibStr : {Γ : Type ℓ}
  {A : Γ → Type ℓ'} (α : FibStr A)
  {B : Γ → Type ℓ''} (β : FibStr B)
  (f : Γ ⊢ A →ᴵ B)
  → FibStr (IsEquivᴵ f)
IsEquivFibStr α β f =
  ΠFibStr β (IsContrFibStr (FiberFibStr (reindexFibStr α _) (reindexFibStr β _) _ _))

reindexIsEquivFibStr : {Δ : Type ℓ} {Γ : Type ℓ'}
  {A : Γ → Type ℓ''} (α : FibStr A)
  {B : Γ → Type ℓ'''} (β : FibStr B)
  {f : Γ ⊢ A →ᴵ B}
  (ρ : Δ → Γ)
  → reindexFibStr (IsEquivFibStr α β f) ρ
    ≡ IsEquivFibStr (reindexFibStr α ρ) (reindexFibStr β ρ) (f ∘ ρ)
reindexIsEquivFibStr α β ρ =
  reindexΠFibStr _ _ _
  ∙ cong (ΠFibStr _)
      (reindexIsContrFibStr _ _ ∙ cong IsContrFibStr (reindexFiberFibStr _ _ _))

Equiv : (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')
Equiv A B = Σ (A → B) IsEquiv

Equivᴵ : {Γ : Type ℓ} (A : Γ → Type ℓ') (B : Γ → Type ℓ'') → (Γ → Type (ℓ' ⊔ ℓ''))
Equivᴵ A B = Σᴵ (A →ᴵ B) (IsEquivᴵ snd)

-- TODO rename?
equivFun : {Γ : Type ℓ} {A : Γ → Type ℓ'} {B : Γ → Type ℓ''}
  → Γ ⊢ Equivᴵ A B
  → Γ ⊢ A →ᴵ B
equivFun = fst ∘_

opaque
  EquivFibStr : {Γ : Type ℓ}
    {A : Γ → Type ℓ'} (α : FibStr A)
    {B : Γ → Type ℓ''} (β : FibStr B)
    → FibStr (Equivᴵ A B)
  EquivFibStr α β =
    ΣFibStr
      (ΠFibStr α (reindexFibStr β fst))
      (IsEquivFibStr (reindexFibStr α fst) (reindexFibStr β fst) _)

  reindexEquivFibStr : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A : Γ → Type ℓ''} (α : FibStr A)
    {B : Γ → Type ℓ'''} (β : FibStr B)
    (ρ : Δ → Γ)
    → reindexFibStr (EquivFibStr α β) ρ
      ≡ EquivFibStr (reindexFibStr α ρ) (reindexFibStr β ρ)
  reindexEquivFibStr α β ρ =
    reindexΣFibStr _ _ _
    ∙ cong₂ (λ α β → ΣFibStr α β)
        (reindexΠFibStr _ _ _)
        (reindexIsEquivFibStr (reindexFibStr α fst) _ _)

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

idEquivFib : (A : Fib ℓ 𝟙) → Equiv (A .fst tt) (A .fst tt)
idEquivFib (_ , α) = idEquiv α

coerceEquiv : (S : Shape)
  {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A)
  (r s : ⟨ S ⟩) → Equiv (A r) (A s)
coerceEquiv S {A} α r s =
  coerce S r
    (EquivFibStr (reindexFibStr α (λ _ → r)) α)
    (idEquiv (reindexFibStr α (λ _ → r)))
    s

opaque
  coerceEquivCap : (S : Shape)
    {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A)
    (r : ⟨ S ⟩) → coerceEquiv S α r r ≡ idEquiv (reindexFibStr α (λ _ → r))
  coerceEquivCap S {A} α r =
    coerceCap S r
      (EquivFibStr (reindexFibStr α (λ _ → r)) α)
      (idEquiv (reindexFibStr α (λ _ → r)))

  coerceEquivVary : ∀ {ℓ} {S T : Shape} (σ : ShapeHom S T)
    {A : ⟨ T ⟩ → Type ℓ} (α : FibStr A)
    (r s : ⟨ S ⟩)
    → coerceEquiv T α (⟪ σ ⟫ r) (⟪ σ ⟫ s) ≡ coerceEquiv S (reindexFibStr α ⟪ σ ⟫) r s
  coerceEquivVary {S = S} σ α r s =
    coerceVary σ r
      (EquivFibStr (reindexFibStr α (λ _ → ⟪ σ ⟫ r)) α)
      (idEquiv (reindexFibStr α (λ _ → ⟪ σ ⟫ r)))
      s
    ∙
    cong
      (λ β → coerce S r β (idEquiv (reindexFibStr α (λ _ → ⟪ σ ⟫ r))) s)
      (reindexEquivFibStr (reindexFibStr α (λ _ → ⟪ σ ⟫ r)) α ⟪ σ ⟫)
