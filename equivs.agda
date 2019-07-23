{-

Definitions of contractible, fibers, equivalences.

-}
{-# OPTIONS --rewriting #-}
module equivs where

open import prelude
open import shape
open import cofprop
open import fibrations
open import Data.paths
open import Data.products
open import Data.functions

----------------------------------------------------------------------
-- IsContr
----------------------------------------------------------------------

IsContr : ∀ {ℓ} → Set ℓ → Set ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContr' : ∀ {ℓ ℓ'} {Γ : Set ℓ} → (Γ → Set ℓ') → (Γ → Set ℓ')
IsContr' A x = IsContr (A x)

abstract
  FibIsContr : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A : Γ → Set ℓ'}
    → isFib A → isFib (IsContr' A)
  FibIsContr {A = A} α =
    FibΣ
      α
      (FibΠ
        (reindex A α fst)
        (reindex (Path' A) (FibPath α) (λ {((x , a₀) , a) → x , a , a₀})))

  reindexIsContr : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set ℓ''}
    (α : isFib A)
    (ρ : Δ → Γ)
    → reindex (IsContr' A) (FibIsContr α) ρ ≡ FibIsContr (reindex A α ρ)
  reindexIsContr {A = A} α ρ =
    trans
      (cong (FibΣ (reindex A α ρ))
        (trans
          (cong
            (λ β →
              FibΠ (reindex A α (ρ ∘ fst))
                (reindex (Path' (λ x → A (ρ x))) β (λ {((x , a₀) , a) → x , a , a₀})))
            (reindexPath _ _ ρ))
          (reindexΠ _ _ _ _ (ρ ×id))))
      (reindexΣ _ _ _ _ ρ)

----------------------------------------------------------------------
-- Fiber type
----------------------------------------------------------------------

Fiber : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} (f : A → B) (b : B) → Set ℓ
Fiber f b = Σ a ∈ _ , f a ~ b

Fiber' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ')
  → Σ (Σ x ∈ Γ , (A x → B x)) (B ∘ fst) → Set ℓ'
Fiber' A B = Σ' (A ∘ fst ∘ fst) (λ {(((x , f) , b) , a) → Path' B (x , f a , b)})

abstract
  FibFiber : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
    → isFib A → isFib B → isFib (Fiber' A B)
  FibFiber {A = A} {B} α β =
    FibΣ
      (reindex A α (fst ∘ fst))
      (reindex (Path' B) (FibPath β) (λ {(((x , f) , b) , a) → (x , f a , b)}))

  reindexFiber : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A B : Γ → Set ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (Fiber' A B) (FibFiber α β) (ρ ×id ×id) ≡ FibFiber (reindex A α ρ) (reindex B β ρ)
  reindexFiber {A = A} {B} α β ρ =
    trans
      (cong
        (λ δ →
          FibΣ (reindex A α (ρ ∘ fst ∘ fst))
            (reindex (Path' (B ∘ ρ)) δ (λ {(((x , f) , b) , a) → (x , f a , b)})))
        (reindexPath _ _ ρ))
      (reindexΣ _ _ _ _ (ρ ×id ×id))

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

FibIsEquiv : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
  → isFib A → isFib B → isFib (IsEquiv' A B)
FibIsEquiv {A = A} {B} α β =
  FibΠ (reindex B β fst) (FibIsContr (FibFiber α β))

reindexIsEquiv : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} {A B : Γ → Set ℓ''}
  (α : isFib A) (β : isFib B)
  (ρ : Δ → Γ)
  → reindex (IsEquiv' A B) (FibIsEquiv α β) (ρ ×id) ≡ FibIsEquiv (reindex A α ρ) (reindex B β ρ)
reindexIsEquiv {A = A} {B} α β ρ =
  trans
    (cong (FibΠ (reindex B β (ρ ∘ fst)))
      (trans
        (cong FibIsContr (reindexFiber α β ρ))
        (reindexIsContr (FibFiber α β) (ρ ×id ×id))))
    (reindexΠ _ _ _ _ (ρ ×id))

Equiv : ∀ {ℓ} (A B : Set ℓ) → Set ℓ
Equiv A B = Σ (A → B) IsEquiv

Equiv' : ∀ {ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ') → (Γ → Set ℓ')
Equiv' A B = Σ' (Π' A (B ∘ fst)) (IsEquiv' A B)

equivFun : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
  → Π (Equiv' A B) → Π (Π' A (B ∘ fst))
equivFun fe x = fe x .fst

abstract
  FibEquiv : ∀ {ℓ ℓ'} {Γ : Set ℓ} {A B : Γ → Set ℓ'}
    → isFib A → isFib B → isFib (Equiv' A B)
  FibEquiv {A = A} {B} α β =
    FibΣ (FibΠ α (reindex B β fst)) (FibIsEquiv α β)

  reindexEquiv : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} {A B : Γ → Set ℓ''}
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (Equiv' A B) (FibEquiv α β) ρ ≡ FibEquiv (reindex A α ρ) (reindex B β ρ)
  reindexEquiv α β ρ =
    trans
      (cong₂ FibΣ
        (reindexΠ _ _ _ _ ρ)
        (reindexIsEquiv α β ρ))
      (reindexΣ _ _ _ _ ρ)

----------------------------------------------------------------------
-- Identity and coercion maps are equivalences
----------------------------------------------------------------------

abstract
  idEquiv : ∀ {ℓ} {A : Set ℓ} → isFib {Γ = Unit} (λ _ → A) → Equiv A A
  idEquiv α .fst = λ a → a
  idEquiv α .snd a .fst = (a , refl~ a)
  idEquiv α .snd a .snd (a' , p) =
    path
      (λ i →
        ( q i .comp O  .fst
        , path (λ j → q i .comp j .fst) refl (q i .cap)
        ))
      (FiberExt
        (trans (p .atO) (symm (q O .comp O .snd ∣ inl refl ∣)))
        (λ j → symm (q O .comp j .snd ∣ inl refl ∣)))
      (FiberExt
        (symm (q I .comp O .snd ∣ inr refl ∣))
        (λ j → symm (q I .comp j .snd ∣ inr refl ∣)))
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

abstract
  coerce : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ} (α : isFib A)
    → (r s : ⟨ S ⟩) → A r → A s
  coerce S α r s a =
    α .lift S r id (int ∋ O ≈ I) (λ v _ → O≠I v) (a , λ v → O≠I v) .comp s .fst

  coerceCap : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ} (α : isFib A)
    → (r : ⟨ S ⟩) → ∀ a → coerce S α r r a ≡ a
  coerceCap S α r a =
    α .lift S r id (int ∋ O ≈ I) (λ v _ → O≠I v) (a , λ v → O≠I v) .cap

  varyCoerce : ∀ {ℓ} (S T : Shape) (σ : ShapeHom S T)
    {A : ⟨ T ⟩ → Set ℓ} (α : isFib A) (r s : ⟨ S ⟩)
    → ∀ a → coerce T α (⟪ σ ⟫ r) (⟪ σ ⟫ s) a ≡ coerce S (reindex A α ⟪ σ ⟫) r s a
  varyCoerce S T σ α r s a =
    α .vary S T σ r id (int ∋ O ≈ I) (λ v _ → O≠I v) (a , λ v → O≠I v) s


coerceEquiv : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ}
  (α : isFib A) (r s : ⟨ S ⟩)
  → Equiv (A r) (A s)
coerceEquiv S {A} α r s =
  coerce S
    (FibEquiv (reindex A α (λ _ → r)) α)
    r s
    (idEquiv (reindex A α (λ _ → r)))

coerceEquivCap : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ}
  (α : isFib A) (r : ⟨ S ⟩)
  → coerceEquiv S α r r ≡ idEquiv (reindex A α (λ _ → r))
coerceEquivCap S {A} α r =
  coerceCap S
    (FibEquiv (reindex A α (λ _ → r)) α)
    r
    (idEquiv (reindex A α (λ _ → r)))

varyCoerceEquiv : ∀ {ℓ} (S T : Shape) (σ : ShapeHom S T)
  {A : ⟨ T ⟩ → Set ℓ} (α : isFib A) (r s : ⟨ S ⟩)
  → coerceEquiv T α (⟪ σ ⟫ r) (⟪ σ ⟫ s) ≡ coerceEquiv S (reindex A α ⟪ σ ⟫) r s
varyCoerceEquiv S T σ {A = A} α r s =
  trans
    (cong
      (λ β → coerce S  β r s (idEquiv (reindex A α (λ _ → ⟪ σ ⟫ r))))
      (reindexEquiv (reindex A α (λ _ → ⟪ σ ⟫ r)) α ⟪ σ ⟫))
    (varyCoerce S T σ
      (FibEquiv (reindex A α (λ _ → ⟪ σ ⟫ r)) α)
      r s
      (idEquiv (reindex A α (λ _ → ⟪ σ ⟫ r))))
