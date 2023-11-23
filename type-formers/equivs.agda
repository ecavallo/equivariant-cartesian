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

private variable ℓ ℓ' ℓ'' : Level

----------------------------------------------------------------------
-- IsContr
----------------------------------------------------------------------

IsContr : Type ℓ → Type ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContrᴵ : {Γ : Type ℓ} → (Γ → Type ℓ') → (Γ → Type ℓ')
IsContrᴵ A x = IsContr (A x)

opaque
  IsContrIsFib : {Γ : Type ℓ} {A : Γ → Type ℓ'}
    → isFib A → isFib (IsContrᴵ A)
  IsContrIsFib α =
    ΣIsFib
      α
      (ΠIsFib
        (reindex α fst)
        (PathIsFib (reindex α (fst ∘ fst)) snd (snd ∘ fst)))

  reindexIsContr : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A : Γ → Type ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → reindex (IsContrIsFib α) ρ ≡ IsContrIsFib (reindex α ρ)
  reindexIsContr α ρ =
    reindexΣ _ _ _
    ∙ cong (ΣIsFib _) (reindexΠ _ _ _ ∙ cong (ΠIsFib _) (reindexPath _ _))

----------------------------------------------------------------------
-- Fiber type
----------------------------------------------------------------------

Fiber : {A : Type ℓ} {B : Type ℓ} (f : A → B) (b : B) → Type ℓ
Fiber f b = Σ a ∈ _ , f a ~ b

Fiberᴵ : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
  (f : Γ ⊢ A →ᴵ B)
  (b : Γ ⊢ B)
  → Γ → Type ℓ'
Fiberᴵ f b γ = Fiber (f γ) (b γ)

opaque
  FiberIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
    (α : isFib A) (b : isFib B)
    (f : Γ ⊢ A →ᴵ B)
    (b : Γ ⊢ B)
    → isFib (Fiberᴵ f b)
  FiberIsFib α β f b =
    ΣIsFib α (PathIsFib (reindex β fst) _ _)

  reindexFiber : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A B : Γ → Type ℓ''}
    (α : isFib A) (β : isFib B)
    {f : Γ ⊢ A →ᴵ B}
    {b : Γ ⊢ B}
    (ρ : Δ → Γ)
    → reindex (FiberIsFib α β f b) ρ ≡ FiberIsFib (reindex α ρ) (reindex β ρ) (f ∘ ρ) (b ∘ ρ)
  reindexFiber α β ρ =
    reindexΣ _ _ _ ∙ cong (ΣIsFib _) (reindexPath _ _)

FiberExt : {A B : Type ℓ} {f : A → B} {b : B} {x y : Fiber f b}
  → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → x ≡ y
FiberExt refl p = Σext refl (PathExt p)

FiberExtDep : {A B : Type ℓ} {f : A → B} {b b' : B} (p : b ≡ b')
  {x : Fiber f b} {y : Fiber f b'}
  → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → subst (Fiber f) p x ≡ y
FiberExtDep refl = FiberExt

eqToFiber : {A B : Type ℓ} {f : A → B} {b : B} (a : A) → f a ≡ b → Fiber f b
eqToFiber a eq = (a , eqToPath eq)

fiberPathEq : {A B : Type ℓ} {f : A → B} {b : B} {x y : Fiber f b}
  → x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEq refl _ = refl

fiberPathEqDep : {A B : Type ℓ} {f : A → B} {b b' : B} (p : b ≡ b')
  {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEqDep refl refl _ = refl

fiberDomEqDep : {A B : Type ℓ} {f : A → B} {b b' : B} (p : b ≡ b')
  {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → x .fst ≡ y .fst
fiberDomEqDep refl refl = refl

----------------------------------------------------------------------
-- Equivalences
----------------------------------------------------------------------

IsEquiv : {A B : Type ℓ} → (A → B) → Type ℓ
IsEquiv f = ∀ b → IsContr (Fiber f b)

IsEquivᴵ : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
  (f : Γ ⊢ A →ᴵ B)
  → Γ → Type ℓ'
IsEquivᴵ f = Πᴵ _ (IsContrᴵ (Fiberᴵ (f ∘ fst) snd))

IsEquivIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
  (α : isFib A) (β : isFib B)
  (f : Γ ⊢ A →ᴵ B)
  → isFib (IsEquivᴵ f)
IsEquivIsFib α β f =
  ΠIsFib β (IsContrIsFib (FiberIsFib (reindex α fst) (reindex β fst) _ _))

reindexIsEquiv : {Δ : Type ℓ} {Γ : Type ℓ'} {A B : Γ → Type ℓ''}
  (α : isFib A) (β : isFib B) {f : Γ ⊢ A →ᴵ B}
  (ρ : Δ → Γ)
  → reindex (IsEquivIsFib α β f) ρ ≡ IsEquivIsFib (reindex α ρ) (reindex β ρ) (f ∘ ρ)
reindexIsEquiv α β ρ =
  reindexΠ _ _ _
  ∙ cong (ΠIsFib _) (reindexIsContr _ _ ∙ cong IsContrIsFib (reindexFiber _ _ _))

Equiv : (A B : Type ℓ) → Type ℓ
Equiv A B = Σ (A → B) IsEquiv

Equivᴵ : {Γ : Type ℓ} (A B : Γ → Type ℓ') → (Γ → Type ℓ')
Equivᴵ A B = Σᴵ (A →ᴵ B) (IsEquivᴵ snd)

equivFun : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
  → Γ ⊢ Equivᴵ A B
  → Γ ⊢ A →ᴵ B
equivFun fe x = fe x .fst

opaque
  EquivIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
    → isFib A → isFib B → isFib (Equivᴵ A B)
  EquivIsFib {A = A} {B} α β =
    ΣIsFib (ΠIsFib α (reindex β fst)) (IsEquivIsFib (reindex α fst) (reindex β fst) _)

  reindexEquiv : {Δ : Type ℓ} {Γ : Type ℓ'} {A B : Γ → Type ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (EquivIsFib α β) ρ ≡ EquivIsFib (reindex α ρ) (reindex β ρ)
  reindexEquiv α β ρ =
    reindexΣ _ _ _ ∙ cong₂ ΣIsFib (reindexΠ _ _ _) (reindexIsEquiv (reindex α fst) _ _)

----------------------------------------------------------------------
-- Identity and coercion maps are equivalences
----------------------------------------------------------------------

idEquiv : {A : Type ℓ} → isFib (λ (_ : 𝟙) → A) → Equiv A A
idEquiv α .fst a = a
idEquiv α .snd a .fst = (a , refl~ a)
idEquiv {A = A} α .snd a .snd (a' , p) = h
  where
  qBox : (i : 𝕀) → OpenBox 𝕚 1 (λ _ → A)
  qBox i .cof = ∂ i
  qBox i .tube =
    OI-rec i
      (λ {refl → p .at})
      (λ {refl _ → a})
  qBox i .cap .out = a
  qBox i .cap .out≡ =
    OI-elim i
      (λ {refl → p .at1})
      (λ {refl → refl})

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

coerceEquiv : (S : Shape) {A : ⟨ S ⟩ → Type ℓ}
  (α : isFib A) (r s : ⟨ S ⟩)
  → Equiv (A r) (A s)
coerceEquiv S {A} α r s =
  coerce S r
    (EquivIsFib (reindex α (λ _ → r)) α)
    (idEquiv (reindex α (λ _ → r)))
    s

opaque
  coerceEquivCap : (S : Shape) {A : ⟨ S ⟩ → Type ℓ}
    (α : isFib A) (r : ⟨ S ⟩)
    → coerceEquiv S α r r ≡ idEquiv (reindex α (λ _ → r))
  coerceEquivCap S {A} α r =
    coerceCap S r
      (EquivIsFib (reindex α (λ _ → r)) α)
      (idEquiv (reindex α (λ _ → r)))

  coerceEquivVary : ∀ {ℓ} {S T : Shape} (σ : ShapeHom S T)
    {A : ⟨ T ⟩ → Type ℓ} (α : isFib A) (r s : ⟨ S ⟩)
    → coerceEquiv T α (⟪ σ ⟫ r) (⟪ σ ⟫ s) ≡ coerceEquiv S (reindex α ⟪ σ ⟫) r s
  coerceEquivVary {S = S} σ α r s =
    coerceVary σ r
      (EquivIsFib (reindex α (λ _ → ⟪ σ ⟫ r)) α)
      (idEquiv (reindex α (λ _ → ⟪ σ ⟫ r)))
      s
    ∙
    cong
      (λ β → coerce S r β (idEquiv (reindex α (λ _ → ⟪ σ ⟫ r))) s)
      (reindexEquiv (reindex α (λ _ → ⟪ σ ⟫ r)) α ⟪ σ ⟫)
