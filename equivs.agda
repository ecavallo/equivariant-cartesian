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

----------------------------------------------------------------------
-- Contr and Ext (now called SContr)
----------------------------------------------------------------------

Contr : Set → Set
Contr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

Contr' : ∀ {ℓ} {Γ : Set ℓ} → (Γ → Set) → Set ℓ
Contr' A = (x : _) → Contr (A x)

----------------------------------------------------------------------
-- Equivalences and quasi-inverses
----------------------------------------------------------------------

Fiber : {A B : Set} (f : A → B) (b : B) → Set
Fiber {A} f b = Σ a ∈ A , f a ~ b

Fiber' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : (x : Γ) → A x → B x) → Σ Γ B → Set
Fiber' f (x , b) = Fiber (f x) b

Equiv : {A B : Set} (f : A → B) → Set
Equiv {B = B} f = (b : B) → Contr (Fiber f b)

Equiv' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : (x : Γ) → A x → B x) → Set ℓ
Equiv' {Γ = Γ} f = (x : Γ) → Equiv (f x)

Qinv : {A B : Set} (f : A → B) → Set
Qinv {A} {B} f = Σ g ∈ (B → A) , ((b : B) → f (g b) ~ b) × ((a : A) → g (f a) ~ a)

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

-- The identity map on a fibration is an equivalence
idEquiv : ∀ {ℓ} {Γ : Set ℓ} {A : Γ → Set} → isFib A → Equiv' {A = A} (λ _ → id)
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
