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
        (reindex (PathIsFib α) (λ ((x , a₀) , a) → x , a , a₀)))

  reindexIsContr : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A : Γ → Type ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → reindex (IsContrIsFib α) ρ ≡ IsContrIsFib (reindex α ρ)
  reindexIsContr α ρ =
    reindexΣ _ _ ρ
    ∙
    cong (ΣIsFib (reindex α ρ))
      (reindexΠ _ _ (ρ ×id)
        ∙ cong
            (λ β →
              ΠIsFib (reindex α (ρ ∘ fst))
                (reindex β (λ ((x , a₀) , a) → x , a , a₀)))
            (reindexPath _ ρ))

----------------------------------------------------------------------
-- Fiber type
----------------------------------------------------------------------

Fiber : {A : Type ℓ} {B : Type ℓ} (f : A → B) (b : B) → Type ℓ
Fiber f b = Σ a ∈ _ , f a ~ b

Fiberᴵ : {Γ : Type ℓ} (A B : Γ → Type ℓ')
  → Σ (Σ x ∈ Γ , (A x → B x)) (B ∘ fst) → Type ℓ'
Fiberᴵ A B = Σᴵ (A ∘ fst ∘ fst) (λ (((x , f) , b) , a) → Pathᴵ B (x , f a , b))

opaque
  FiberIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
    → isFib A → isFib B → isFib (Fiberᴵ A B)
  FiberIsFib {A = A} {B} α β =
    ΣIsFib
      (reindex α (fst ∘ fst))
      (reindex (PathIsFib β) (λ (((x , f) , b) , a) → (x , f a , b)))

  reindexFiber : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A B : Γ → Type ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (FiberIsFib α β) (ρ ×id ×id) ≡ FiberIsFib (reindex α ρ) (reindex β ρ)
  reindexFiber {A = A} {B} α β ρ =
    reindexΣ _ _ (ρ ×id ×id)
    ∙ cong
        (λ δ →
          ΣIsFib (reindex α (ρ ∘ fst ∘ fst))
            (reindex δ (λ (((x , f) , b) , a) → (x , f a , b))))
        (reindexPath β ρ)

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

IsEquivᴵ : {Γ : Type ℓ} (A B : Γ → Type ℓ')
  → Σ Γ (λ x → A x → B x) → Type ℓ'
IsEquivᴵ A B = Πᴵ (B ∘ fst) (IsContrᴵ (Fiberᴵ A B))

IsEquivIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
  → isFib A → isFib B → isFib (IsEquivᴵ A B)
IsEquivIsFib {A = A} {B} α β =
  ΠIsFib (reindex β fst) (IsContrIsFib (FiberIsFib α β))

reindexIsEquiv : {Δ : Type ℓ} {Γ : Type ℓ'} {A B : Γ → Type ℓ''}
  (α : isFib A) (β : isFib B)
  (ρ : Δ → Γ)
  → reindex (IsEquivIsFib α β) (ρ ×id) ≡ IsEquivIsFib (reindex α ρ) (reindex β ρ)
reindexIsEquiv {A = A} {B} α β ρ =
  reindexΠ _ _ (ρ ×id)
  ∙ cong (ΠIsFib (reindex β (ρ ∘ fst)))
      (reindexIsContr (FiberIsFib α β) (ρ ×id ×id)
        ∙ cong IsContrIsFib (reindexFiber α β ρ))

Equiv : (A B : Type ℓ) → Type ℓ
Equiv A B = Σ (A → B) IsEquiv

Equivᴵ : {Γ : Type ℓ} (A B : Γ → Type ℓ') → (Γ → Type ℓ')
Equivᴵ A B = Σᴵ (A →ᴵ B) (IsEquivᴵ A B)

equivFun : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
  → Γ ⊢ Equivᴵ A B
  → Γ ⊢ A →ᴵ B
equivFun fe x = fe x .fst

opaque
  EquivIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
    → isFib A → isFib B → isFib (Equivᴵ A B)
  EquivIsFib {A = A} {B} α β =
    ΣIsFib (ΠIsFib α (reindex β fst)) (IsEquivIsFib α β)

  reindexEquiv : {Δ : Type ℓ} {Γ : Type ℓ'} {A B : Γ → Type ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (EquivIsFib α β) ρ ≡ EquivIsFib (reindex α ρ) (reindex β ρ)
  reindexEquiv α β ρ =
    reindexΣ _ _ ρ ∙ cong₂ ΣIsFib (reindexΠ _ _ ρ) (reindexIsEquiv α β ρ)

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

  coerceEquivVary : ∀ {ℓ} (S T : Shape) (σ : ShapeHom S T)
    {A : ⟨ T ⟩ → Type ℓ} (α : isFib A) (r s : ⟨ S ⟩)
    → coerceEquiv T α (⟪ σ ⟫ r) (⟪ σ ⟫ s) ≡ coerceEquiv S (reindex α ⟪ σ ⟫) r s
  coerceEquivVary S T σ {A = A} α r s =
    coerceVary S T σ r
      (EquivIsFib (reindex α (λ _ → ⟪ σ ⟫ r)) α)
      (idEquiv (reindex α (λ _ → ⟪ σ ⟫ r)))
      s
    ∙
    cong
      (λ β → coerce S r β (idEquiv (reindex α (λ _ → ⟪ σ ⟫ r))) s)
      (reindexEquiv (reindex α (λ _ → ⟪ σ ⟫ r)) α ⟪ σ ⟫)
