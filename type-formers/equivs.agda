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

private variable ℓ ℓ' : Level

----------------------------------------------------------------------
-- IsContr
----------------------------------------------------------------------

IsContr : ∀ {ℓ} → Set ℓ → Set ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContr' : ∀ {ℓ ℓ'} {Γ : Set ℓ} → (Γ → Set ℓ') → (Γ → Set ℓ')
IsContr' A x = IsContr (A x)

opaque
  IsContrIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A : Γ → Set ℓ'}
    → isFib A → isFib (IsContr' A)
  IsContrIsFib α =
    ΣIsFib
      α
      (ΠIsFib
        (reindex α fst)
        (reindex (PathIsFib α) (λ ((x , a₀) , a) → x , a , a₀)))

  reindexIsContr : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set ℓ''}
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

Fiber : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} (f : A → B) (b : B) → Set ℓ
Fiber f b = Σ a ∈ _ , f a ~ b

Fiber' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ')
  → Σ (Σ x ∈ Γ , (A x → B x)) (B ∘ fst) → Set ℓ'
Fiber' A B = Σ' (A ∘ fst ∘ fst) (λ (((x , f) , b) , a) → Path' B (x , f a , b))

opaque
  FiberIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
    → isFib A → isFib B → isFib (Fiber' A B)
  FiberIsFib {A = A} {B} α β =
    ΣIsFib
      (reindex α (fst ∘ fst))
      (reindex (PathIsFib β) (λ (((x , f) , b) , a) → (x , f a , b)))

  reindexFiber : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A B : Γ → Set ℓ''}
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

FiberExt : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {b : B} {x y : Fiber f b}
  → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → x ≡ y
FiberExt refl p = Σext refl (PathExt p)

FiberExtDep : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {b b' : B} (p : b ≡ b')
  {x : Fiber f b} {y : Fiber f b'}
  → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → subst (Fiber f) p x ≡ y
FiberExtDep refl = FiberExt

eqToFiber : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {b : B} (a : A) → f a ≡ b → Fiber f b
eqToFiber a eq = (a , eqToPath eq)

fiberPathEq : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {b : B} {x y : Fiber f b}
  → x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEq refl _ = refl

fiberPathEqDep : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {b b' : B} (p : b ≡ b')
  {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEqDep refl refl _ = refl

fiberDomEqDep : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {b b' : B} (p : b ≡ b')
  {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → x .fst ≡ y .fst
fiberDomEqDep refl refl = refl

----------------------------------------------------------------------
-- Equivalences
----------------------------------------------------------------------

IsEquiv : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Set ℓ
IsEquiv f = ∀ b → IsContr (Fiber f b)

IsEquiv' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ')
  → Σ Γ (λ x → A x → B x) → Set ℓ'
IsEquiv' A B = Π' (B ∘ fst) (IsContr' (Fiber' A B))

IsEquivIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
  → isFib A → isFib B → isFib (IsEquiv' A B)
IsEquivIsFib {A = A} {B} α β =
  ΠIsFib (reindex β fst) (IsContrIsFib (FiberIsFib α β))

reindexIsEquiv : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} {A B : Γ → Set ℓ''}
  (α : isFib A) (β : isFib B)
  (ρ : Δ → Γ)
  → reindex (IsEquivIsFib α β) (ρ ×id) ≡ IsEquivIsFib (reindex α ρ) (reindex β ρ)
reindexIsEquiv {A = A} {B} α β ρ =
  reindexΠ _ _ (ρ ×id)
  ∙ cong (ΠIsFib (reindex β (ρ ∘ fst)))
      (reindexIsContr (FiberIsFib α β) (ρ ×id ×id)
        ∙ cong IsContrIsFib (reindexFiber α β ρ))

Equiv : ∀ {ℓ} (A B : Set ℓ) → Set ℓ
Equiv A B = Σ (A → B) IsEquiv

Equiv' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ') → (Γ → Set ℓ')
Equiv' A B = Σ' (Π' A (B ∘ fst)) (IsEquiv' A B)

equivFun : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
  → Π (Equiv' A B) → Π (Π' A (B ∘ fst))
equivFun fe x = fe x .fst

opaque
  EquivIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
    → isFib A → isFib B → isFib (Equiv' A B)
  EquivIsFib {A = A} {B} α β =
    ΣIsFib (ΠIsFib α (reindex β fst)) (IsEquivIsFib α β)

  reindexEquiv : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} {A B : Γ → Set ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (EquivIsFib α β) ρ ≡ EquivIsFib (reindex α ρ) (reindex β ρ)
  reindexEquiv α β ρ =
    reindexΣ _ _ ρ ∙ cong₂ ΣIsFib (reindexΠ _ _ ρ) (reindexIsEquiv α β ρ)

----------------------------------------------------------------------
-- Identity and coercion maps are equivalences
----------------------------------------------------------------------

idEquiv : ∀ {ℓ} {A : Set ℓ} → isFib {Γ = 𝟙} (λ _ → A) → Equiv A A
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

coerceEquiv : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ}
  (α : isFib A) (r s : ⟨ S ⟩)
  → Equiv (A r) (A s)
coerceEquiv S {A} α r s =
  coerce S r
    (EquivIsFib (reindex α (λ _ → r)) α)
    (idEquiv (reindex α (λ _ → r)))
    s

opaque
  coerceEquivCap : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ}
    (α : isFib A) (r : ⟨ S ⟩)
    → coerceEquiv S α r r ≡ idEquiv (reindex α (λ _ → r))
  coerceEquivCap S {A} α r =
    coerceCap S r
      (EquivIsFib (reindex α (λ _ → r)) α)
      (idEquiv (reindex α (λ _ → r)))

  coerceEquivVary : ∀ {ℓ} (S T : Shape) (σ : ShapeHom S T)
    {A : ⟨ T ⟩ → Set ℓ} (α : isFib A) (r s : ⟨ S ⟩)
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
