{-

Fibrancy of path and homotopy fiber types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.paths where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.coercion
open import type-formers.extension
open import type-formers.pi
open import type-formers.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

record _~_ {A : Type ℓ} (a a' : A) : Type ℓ where
  constructor path
  field
    at : 𝕀 → A
    at0 : at 0 ≡ a
    at1 : at 1 ≡ a'

open _~_ public

eqToPath : {A : Type ℓ} {x y : A} → x ≡ y → x ~ y
eqToPath {x = x} p = path (λ _ → x) refl p

refl~ : {A : Type ℓ} (a : A) → a ~ a
refl~ a = eqToPath refl

PathExt : {A : Type ℓ} {a a' : A} {p q : a ~ a'}
  → (∀ i → p .at i ≡ q .at i) → p ≡ q
PathExt t =
  congΣ (uncurry ∘ path) (funExt t) (×ext uip' uip')

Pathᴵ : (A : Γ → Type ℓ) (a₀ a₁ : Γ ⊢ A) → Γ → Type ℓ
Pathᴵ A a₀ a₁ γ = a₀ γ ~ a₁ γ

opaque
  private
    partialEl : {A : Γ → Type ℓ} (a₀ a₁ : Γ ⊢ A)
      → Γ ▷𝕀 ▷[ ∂ ∘ snd ] ⊢ A ∘ fst ∘ wk[ ∂ ∘ snd ]
    partialEl a₀ a₁ =
      uncurry λ (γ , i) → OI-rec i (λ _ → a₀ γ) (λ _ → a₁ γ)

    retract : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ A}
      → Γ ⊢ Retractᴵ (Pathᴵ A a₀ a₁) (Extensionᴵ 𝕚 (A ∘ fst) ∂ (partialEl a₀ a₁))
    retract γ .sec p i .out = p .at i
    retract γ .sec p i .out≡ =
      OI-elim i (λ {refl → sym (p .at0)}) (λ {refl → sym (p .at1)})
    retract γ .ret ex .at i = ex i .out
    retract γ .ret ex .at0 = sym (ex 0 .out≡ (∨l refl))
    retract γ .ret ex .at1 = sym (ex 1 .out≡ (∨r refl))
    retract γ .inv = funExt' $ PathExt λ _ → refl

  PathFibStr : {A : Γ → Type ℓ} (α : FibStr A) (a₀ a₁ : Γ ⊢ A)
    → FibStr (Pathᴵ A a₀ a₁)
  PathFibStr α a₀ a₁ =
    retractFibStr retract (ExtensionFibStr 𝕚 (α ∘ᶠˢ fst) ∂ _)

  ----------------------------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------------------------

  reindexPathFibStr : {A : Γ → Type ℓ} {α : FibStr A} {a₀ a₁ : Γ ⊢ A}
    (ρ : Δ → Γ)
    → PathFibStr α a₀ a₁ ∘ᶠˢ ρ ≡ PathFibStr (α ∘ᶠˢ ρ) (a₀ ∘ ρ) (a₁ ∘ ρ)
  reindexPathFibStr ρ =
    reindexRetractFibStr retract ρ
    ∙
    cong₂
      retractFibStr
      (funExt' $ retractExt (funExt' $ funExt' $ restrictExt refl) refl)
      (reindexExtensionFibStr ρ)

------------------------------------------------------------------------------------------
-- Fibrant path types
------------------------------------------------------------------------------------------

Pathᶠ : (A : Γ ⊢ᶠType ℓ) (a₀ a₁ : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
Pathᶠ A a₀ a₁ .fst = Pathᴵ (A .fst) a₀ a₁
Pathᶠ A a₀ a₁ .snd = PathFibStr (A .snd) a₀ a₁

reindexPathᶠ : {A : Γ ⊢ᶠType ℓ} {a₀ a₁ : Γ ⊢ A .fst}
  (ρ : Δ → Γ) → Pathᶠ A a₀ a₁ ∘ᶠ ρ ≡ Pathᶠ (A ∘ᶠ ρ) (a₀ ∘ ρ) (a₁ ∘ ρ)
reindexPathᶠ ρ = Σext refl (reindexPathFibStr ρ)

reflᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ A .fst) → Γ ⊢ᶠ Pathᶠ A a a
reflᶠ A = refl~ ∘_

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

  reindexFiberFibStr : {A : Γ → Type ℓ} {α : FibStr A} {B : Γ → Type ℓ'} {β : FibStr B}
    {f : Γ ⊢ A →ᴵ B} {b : Γ ⊢ B}
    (ρ : Δ → Γ)
    → FiberFibStr α β f b ∘ᶠˢ ρ ≡ FiberFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ ρ) (f ∘ ρ) (b ∘ ρ)
  reindexFiberFibStr ρ =
    reindexΣFibStr _ ∙ cong (ΣFibStr _) (reindexPathFibStr _)

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
-- Singleton contractibility
------------------------------------------------------------------------------------------

Singlᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
Singlᶠ A a = Fiberᶠ A A (λ _ → id) a

singlCenterᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  → Γ ⊢ᶠ Singlᶠ A a
singlCenterᶠ A a =
  pairᶠ A (Pathᶠ (A ∘ᶠ fst) snd (a ∘ fst)) a (reflᶠ A a)

singlContrᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  (c : Γ ⊢ᶠ Σᶠ A (Pathᶠ (A ∘ᶠ fst) snd (a ∘ fst)))
  → Γ ⊢ᶠ Pathᶠ (Σᶠ A (Pathᶠ (A ∘ᶠ fst) snd (a ∘ fst))) c (singlCenterᶠ A a)
singlContrᶠ A a c γ = homotopy
  where
  box : (i : 𝕀) → OpenBox 𝕚 1 (λ _ → A .fst γ)
  box i .cof = ∂ i
  box i .tube j = OI-rec i (λ {refl → c γ .snd .at j}) (λ {refl → a γ})
  box i .cap .out = a γ
  box i .cap .out≡ = OI-elim i (λ {refl → c γ .snd .at1}) (λ {refl → refl})

  square : (i : 𝕀) → Filler (box i)
  square i = A .snd .lift 𝕚 1 (λ _ → _) (box i)

  homotopy : c γ ~ (a γ , refl~ (a γ))
  homotopy .at i .fst = square i .fill 0 .out
  homotopy .at i .snd = path (λ j → square i .fill j .out) refl (square i .cap≡)
  homotopy .at0 =
    FiberExt
      (sym (square 0 .fill 0 .out≡ (∨l refl)) ∙ c γ .snd .at0)
      (λ j → sym (square 0 .fill j .out≡ (∨l refl)))
  homotopy .at1 =
    FiberExt
      (sym (square 1 .fill 0 .out≡ (∨r refl)))
      (λ j → sym (square 1 .fill j .out≡ (∨r refl)))

------------------------------------------------------------------------------------------
-- Weak Paulin-Mohring-style J eliminator, stated in terms of singletons
------------------------------------------------------------------------------------------

Jᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  (P : Γ ▷ᶠ Singlᶠ A a ⊢ᶠType ℓ')
  (d : Γ ⊢ᶠ P ∘ᶠ (id ,, singlCenterᶠ A a))
  (c : Γ ⊢ᶠ Singlᶠ A a)
  → Γ ⊢ᶠ P ∘ᶠ (id ,, c)
Jᶠ A a P d c γ =
  subst (P .fst ∘ (γ ,_)) (singlContrᶠ A a c γ .at0)
    (Coerce.coerce 𝕚 1
      (P ∘ᶠ λ i → γ , singlContrᶠ A a c γ .at i)
      (subst (P .fst ∘ (γ ,_)) (sym (singlContrᶠ A a c γ .at1)) (d γ))
      0)
