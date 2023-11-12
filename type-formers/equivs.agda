{-

Definitions of contractible, fibers, equivalences.

-}
{-# OPTIONS --rewriting #-}
module type-formers.equivs where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma

----------------------------------------------------------------------
-- IsContr
----------------------------------------------------------------------

IsContr : ∀ {ℓ} → Set ℓ → Set ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContr' : ∀ {ℓ ℓ'} {Γ : Set ℓ} → (Γ → Set ℓ') → (Γ → Set ℓ')
IsContr' A x = IsContr (A x)

abstract
  IsContrIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A : Γ → Set ℓ'}
    → isFib A → isFib (IsContr' A)
  IsContrIsFib {A = A} α =
    ΣIsFib
      α
      (ΠIsFib
        (reindex A α fst)
        (reindex (Path' A) (PathIsFib α) (λ {((x , a₀) , a) → x , a , a₀})))

  reindexIsContr : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → reindex (IsContr' A) (IsContrIsFib α) ρ ≡ IsContrIsFib (reindex A α ρ)
  reindexIsContr {A = A} α ρ =
    reindexΣ _ _ _ _ ρ
    ∙
    cong (ΣIsFib (reindex A α ρ))
      (reindexΠ _ _ _ _ (ρ ×id)
        ∙ cong
            (λ β →
              ΠIsFib (reindex A α (ρ ∘ fst))
                (reindex (Path' (λ x → A (ρ x))) β (λ {((x , a₀) , a) → x , a , a₀})))
            (reindexPath _ _ ρ))

----------------------------------------------------------------------
-- Fiber type
----------------------------------------------------------------------

Fiber : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} (f : A → B) (b : B) → Set ℓ
Fiber f b = Σ a ∈ _ , f a ~ b

Fiber' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ')
  → Σ (Σ x ∈ Γ , (A x → B x)) (B ∘ fst) → Set ℓ'
Fiber' A B = Σ' (A ∘ fst ∘ fst) (λ {(((x , f) , b) , a) → Path' B (x , f a , b)})

abstract
  FiberIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
    → isFib A → isFib B → isFib (Fiber' A B)
  FiberIsFib {A = A} {B} α β =
    ΣIsFib
      (reindex A α (fst ∘ fst))
      (reindex (Path' B) (PathIsFib β) (λ {(((x , f) , b) , a) → (x , f a , b)}))

  reindexFiber : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A B : Γ → Set ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (Fiber' A B) (FiberIsFib α β) (ρ ×id ×id) ≡ FiberIsFib (reindex A α ρ) (reindex B β ρ)
  reindexFiber {A = A} {B} α β ρ =
    reindexΣ _ _ _ _ (ρ ×id ×id)
    ∙ cong
        (λ δ →
          ΣIsFib (reindex A α (ρ ∘ fst ∘ fst))
            (reindex (Path' (B ∘ ρ)) δ (λ {(((x , f) , b) , a) → (x , f a , b)})))
        (reindexPath _ _ ρ)

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
  ΠIsFib (reindex B β fst) (IsContrIsFib (FiberIsFib α β))

reindexIsEquiv : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} {A B : Γ → Set ℓ''}
  (α : isFib A) (β : isFib B)
  (ρ : Δ → Γ)
  → reindex (IsEquiv' A B) (IsEquivIsFib α β) (ρ ×id) ≡ IsEquivIsFib (reindex A α ρ) (reindex B β ρ)
reindexIsEquiv {A = A} {B} α β ρ =
  reindexΠ _ _ _ _ (ρ ×id)
  ∙ cong (ΠIsFib (reindex B β (ρ ∘ fst)))
      (reindexIsContr (FiberIsFib α β) (ρ ×id ×id)
        ∙ cong IsContrIsFib (reindexFiber α β ρ))

Equiv : ∀ {ℓ} (A B : Set ℓ) → Set ℓ
Equiv A B = Σ (A → B) IsEquiv

Equiv' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ') → (Γ → Set ℓ')
Equiv' A B = Σ' (Π' A (B ∘ fst)) (IsEquiv' A B)

equivFun : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
  → Π (Equiv' A B) → Π (Π' A (B ∘ fst))
equivFun fe x = fe x .fst

abstract
  EquivIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
    → isFib A → isFib B → isFib (Equiv' A B)
  EquivIsFib {A = A} {B} α β =
    ΣIsFib (ΠIsFib α (reindex B β fst)) (IsEquivIsFib α β)

  reindexEquiv : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} {A B : Γ → Set ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (Equiv' A B) (EquivIsFib α β) ρ ≡ EquivIsFib (reindex A α ρ) (reindex B β ρ)
  reindexEquiv α β ρ =
    reindexΣ _ _ _ _ ρ
    ∙ cong₂ ΣIsFib
        (reindexΠ _ _ _ _ ρ)
        (reindexIsEquiv α β ρ)

----------------------------------------------------------------------
-- Identity and coercion maps are equivalences
----------------------------------------------------------------------

idEquiv : ∀ {ℓ} {A : Set ℓ} → isFib {Γ = Unit} (λ _ → A) → Equiv A A
idEquiv α .fst a = a
idEquiv α .snd a .fst = (a , refl~ a)
idEquiv α .snd a .snd (a' , p) = h
  where
  q : (i : Int) → _
  q i =
    α .lift int I (λ _ → tt) (∂ i)
      (OI-rec i
        (λ {refl → p .at})
        (λ {refl _ → a}))
      ( a
      , OI-elim i
        (λ {refl → p .atI})
        (λ {refl → refl})
      )

  h : (a' , p) ~ (a , refl~ a)
  h .at i .fst = q i .comp O  .fst
  h .at i .snd = path (λ j → q i .comp j .fst) refl (q i .cap)
  h .atO =
    FiberExt
      (symm (q O .comp O .snd ∣ inl refl ∣) ∙ p .atO)
      (λ j → symm (q O .comp j .snd ∣ inl refl ∣))
  h .atI =
    FiberExt
      (symm (q I .comp O .snd ∣ inr refl ∣))
      (λ j → symm (q I .comp j .snd ∣ inr refl ∣))

abstract
  coerce : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ} (α : isFib A)
    → (r s : ⟨ S ⟩) → A r → A s
  coerce S α r s a =
    α .lift S r id ⊥ (λ v _ → ∅-rec v) (a , λ v → ∅-rec v) .comp s .fst

  coerceCap : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ} (α : isFib A)
    → (r : ⟨ S ⟩) → ∀ a → coerce S α r r a ≡ a
  coerceCap S α r a =
    α .lift S r id ⊥ (λ v _ → ∅-rec v) (a , λ v → ∅-rec v) .cap

  varyCoerce : ∀ {ℓ} (S T : Shape) (σ : ShapeHom S T)
    {A : ⟨ T ⟩ → Set ℓ} (α : isFib A) (r s : ⟨ S ⟩)
    → ∀ a → coerce T α (⟪ σ ⟫ r) (⟪ σ ⟫ s) a ≡ coerce S (reindex A α ⟪ σ ⟫) r s a
  varyCoerce S T σ α r s a =
    α .vary S T σ r id ⊥ (λ v _ → ∅-rec v) (a , λ v → ∅-rec v) s


coerceEquiv : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ}
  (α : isFib A) (r s : ⟨ S ⟩)
  → Equiv (A r) (A s)
coerceEquiv S {A} α r s =
  coerce S
    (EquivIsFib (reindex A α (λ _ → r)) α)
    r s
    (idEquiv (reindex A α (λ _ → r)))

coerceEquivCap : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ}
  (α : isFib A) (r : ⟨ S ⟩)
  → coerceEquiv S α r r ≡ idEquiv (reindex A α (λ _ → r))
coerceEquivCap S {A} α r =
  coerceCap S
    (EquivIsFib (reindex A α (λ _ → r)) α)
    r
    (idEquiv (reindex A α (λ _ → r)))

varyCoerceEquiv : ∀ {ℓ} (S T : Shape) (σ : ShapeHom S T)
  {A : ⟨ T ⟩ → Set ℓ} (α : isFib A) (r s : ⟨ S ⟩)
  → coerceEquiv T α (⟪ σ ⟫ r) (⟪ σ ⟫ s) ≡ coerceEquiv S (reindex A α ⟪ σ ⟫) r s
varyCoerceEquiv S T σ {A = A} α r s =
  varyCoerce S T σ
    (EquivIsFib (reindex A α (λ _ → ⟪ σ ⟫ r)) α)
    r s
    (idEquiv (reindex A α (λ _ → ⟪ σ ⟫ r)))
  ∙
  cong
    (λ β → coerce S  β r s (idEquiv (reindex A α (λ _ → ⟪ σ ⟫ r))))
    (reindexEquiv (reindex A α (λ _ → ⟪ σ ⟫ r)) α ⟪ σ ⟫)
