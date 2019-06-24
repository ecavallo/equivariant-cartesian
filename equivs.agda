{-

Definitions of contractible, extensible (SContr), fibers, equivalences
and quasi-invertible maps.

-}
{-# OPTIONS --rewriting #-}
module equivs where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.paths
open import Data.products
open import Data.functions

----------------------------------------------------------------------
-- Contr
----------------------------------------------------------------------

Contr : Set → Set
Contr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

Contr' : ∀ {ℓ} {Γ : Set ℓ} → (Γ → Set) → (Γ → Set)
Contr' A x = Contr (A x)

abstract
  FibContr : ∀ {ℓ} {Γ : Set ℓ} {A : Γ → Set}
    → isFib A → isFib (Contr' A)
  FibContr {A = A} α =
    FibΣ
      α
      (FibΠ
        (reindex A α fst)
        (reindex (Path' A) (FibPath α) (λ {((x , a₀) , a) → x , a , a₀})))

  reindexContr : ∀ {ℓ ℓ'} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set}
    (α : isFib A)
    (ρ : Δ → Γ)
    → reindex (Contr' A) (FibContr α) ρ ≡ FibContr (reindex A α ρ)
  reindexContr {A = A} α ρ =
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

Fiber : {A B : Set} (f : A → B) (b : B) → Set
Fiber {A} f b = Σ a ∈ A , f a ~ b

Fiber' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : (x : Γ) → A x → B x) → Σ Γ B → Set
Fiber' f (x , b) = Fiber (f x) b

abstract
  FibFiber : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : ∀ x → A x → B x)
    → isFib A → isFib B → isFib (Fiber' f)
  FibFiber {A = A} {B} f α β =
    FibΣ
      (reindex A α fst)
      (reindex (Path' B) (FibPath β) (λ {((x , b) , a) → (x , f x a , b)}))

  reindexFiber : ∀ {ℓ ℓ'} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set} {B : Γ → Set}
    (f : ∀ x → A x → B x)
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (Fiber' f) (FibFiber f α β) (ρ ×id) ≡ FibFiber (f ∘ ρ) (reindex A α ρ) (reindex B β ρ)
  reindexFiber {A = A} {B} f α β ρ =
    trans
      (cong
        (λ δ →
          FibΣ (reindex A α (ρ ∘ fst))
            (reindex (Path' (λ z → B (ρ z))) δ (λ {((x , b) , a) → (x , f (ρ x) a , b)})))
        (reindexPath _ _ ρ))
      (reindexΣ _ _ _ _ (ρ ×id))

FiberExt : {A B : Set} {f : A → B} {b : B} {x y : Fiber f b}
  → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → x ≡ y
FiberExt refl p = Σext refl (PathExt p)

FiberExtDep : {A B : Set} {f : A → B} {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
  → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → subst (Fiber f) p x ≡ y
FiberExtDep refl = FiberExt

eqToFiber : {A B : Set} {f : A → B} {b : B} (a : A) → f a ≡ b → Fiber f b
eqToFiber a eq = (a , eqToPath eq)

fiberPathEq : {A B : Set} {f : A → B} {b : B} {x y : Fiber f b}
  → x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEq refl _ = refl

fiberPathEqDep : {A B : Set} {f : A → B} {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEqDep refl refl _ = refl

fiberDomEqDep :  {A B : Set} {f : A → B} {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → x .fst ≡ y .fst
fiberDomEqDep refl refl = refl

----------------------------------------------------------------------
-- Equivalences
----------------------------------------------------------------------

Equiv : {A B : Set} (f : A → B) → Set
Equiv {B = B} f = (b : B) → Contr (Fiber f b)

Equiv' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : (x : Γ) → A x → B x) → (Γ → Set)
Equiv' {B = B} f = Π' B (Contr' (Fiber' f))

abstract
  FibEquiv : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : ∀ x → A x → B x)
    → isFib A → isFib B → isFib (Equiv' f)
  FibEquiv {A = A} {B} f α β =
    FibΠ β (FibContr (FibFiber _ α β))

  reindexEquiv : ∀ {ℓ ℓ'} {Δ : Set ℓ} {Γ : Set ℓ'}
    {A : Γ → Set} {B : Γ → Set}
    (f : ∀ x → A x → B x)
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (Equiv' f) (FibEquiv f α β) ρ ≡ FibEquiv (f ∘ ρ) (reindex A α ρ) (reindex B β ρ)
  reindexEquiv f α β ρ =
    trans
      (cong (FibΠ (reindex _ β ρ))
        (trans
          (cong FibContr
            (reindexFiber f α β ρ))
          (reindexContr _ (ρ ×id))))
      (reindexΠ _ _ _ _ ρ)

----------------------------------------------------------------------
-- Identity and coercion maps are equivalences
----------------------------------------------------------------------

idEquiv : ∀ {ℓ} {Γ : Set ℓ} {A : Γ → Set} → isFib A → Π (Equiv' {A = A} (λ _ → id))
idEquiv {A = A} α x a .fst = (a , refl~ a)
idEquiv {A = A} α x a .snd (a' , p) =
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
    α .lift int I (λ _ → x) (∂ i)
      (OI-rec i
        (λ {refl → p .at})
        (λ {refl _ → a}))
      ( a
      , OI-elim i
        (λ {refl → p .atI})
        (λ {refl → refl})
      )

coerce : ∀ {ℓ} {Γ : Set ℓ} (S : Shape) {A : Γ → ⟨ S ⟩ → Set}
  → isFib (uncurry A)
  → (r s : ⟨ S ⟩) → ∀ x → A x r → A x s
coerce S α r s x a =
  α .lift S r (λ s → x , s) (int ∋ O ≈ I) O≠I (a , λ v → O≠I v) .comp s .fst

coerceCap : ∀ {ℓ} {Γ : Set ℓ} (S : Shape) {A : Γ → ⟨ S ⟩ → Set}
  (α : isFib (uncurry A))
  → (r : ⟨ S ⟩) → ∀ x a → coerce S α r r x a ≡ a
coerceCap S α r x a =
  α .lift S r (λ s → x , s) (int ∋ O ≈ I) O≠I (a , λ v → O≠I v) .cap

coerceEquiv : ∀ {ℓ} {Γ : Set ℓ} (S : Shape) {A : Γ → ⟨ S ⟩ → Set}
  (α : isFib (uncurry A))
  → (r s : ⟨ S ⟩) → Π (Equiv' (coerce S α r s))
coerceEquiv {Γ = Γ} S {A} α r s x =
  coerce S equivTy r s x
    (subst
      Equiv
      (funext λ a → symm (coerceCap S α r x a))
      (idEquiv (reindex _ α (λ {x → (x , r)})) x))
  where
  equivTy = FibEquiv (λ {(x , i) → coerce S α r i x}) (reindex _ α (λ {(x , i) → (x , r)})) α
