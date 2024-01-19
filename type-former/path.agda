{-

Fibrancy of path and homotopy fiber types.

-}
module type-former.path where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration
open import fibration.transport
open import type-former.extension
open import type-former.pi
open import type-former.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

record _~_ {A : Type ℓ} (a₀ a₁ : A) : Type ℓ where
  constructor path
  field
    at : 𝕀 → A
    at0 : at 0 ≡ a₀
    at1 : at 1 ≡ a₁

open _~_ public

eqToPath : {A : Type ℓ} {a₀ a₁ : A} → a₀ ≡ a₁ → a₀ ~ a₁
eqToPath {a₀ = a₀} eq = path (cst a₀) refl eq

refl~ : {A : Type ℓ} (a : A) → a ~ a
refl~ a = eqToPath refl

congPath : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {a₀ a₁ : A}
  → a₀ ~ a₁ → f a₀ ~ f a₁
congPath f p .at = f ∘ p .at
congPath f p .at0 = cong f (p .at0)
congPath f p .at1 = cong f (p .at1)

PathExt : {A : Type ℓ} {a₀ a₁ : A} {p q : a₀ ~ a₁}
  → (∀ i → p .at i ≡ q .at i) → p ≡ q
PathExt t =
  congΣ (uncurry ∘ path) (funExt t) (×ext uip' uip')

Pathˣ : (A : Γ → Type ℓ) (a₀ a₁ : Γ ⊢ˣ A) → Γ → Type ℓ
Pathˣ A a₀ a₁ γ = a₀ γ ~ a₁ γ

congPathˣ : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
  (f : Γ ⊢ˣ A →ˣ B)
  {a₀ a₁ : Γ ⊢ˣ A} (p : Γ ⊢ˣ Pathˣ A a₀ a₁)
  → Γ ⊢ˣ Pathˣ B (appˣ f a₀) (appˣ f a₁)
congPathˣ f p γ = congPath (f γ) (p γ)

opaque
  private
    partialEl : {A : Γ → Type ℓ} (a₀ a₁ : Γ ⊢ˣ A)
      → Γ ▷𝕀 ▷[ ∂ ∘ 𝒒 ] ⊢ˣ (A ∘ 𝒑) ↾ (∂ ∘ 𝒒)
    partialEl a₀ a₁ =
      uncurry λ (γ , i) → ∂-rec i (λ _ → a₀ γ) (λ _ → a₁ γ)

    retract : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ˣ A}
      → Γ ⊢ˣ Retractˣ (Pathˣ A a₀ a₁) (Extensionˣ 𝕚 (A ∘ 𝒑) ∂ (partialEl a₀ a₁))
    retract γ .sec p i .out = p .at i
    retract γ .sec p i .out≡ =
      ∂-elim i (λ {refl → sym (p .at0)}) (λ {refl → sym (p .at1)})
    retract γ .ret ex .at i = ex i .out
    retract γ .ret ex .at0 = sym (ex 0 .out≡ (∨l refl))
    retract γ .ret ex .at1 = sym (ex 1 .out≡ (∨r refl))
    retract γ .inv _ = PathExt λ _ → refl

  PathFibStr : {A : Γ → Type ℓ} (α : FibStr A) (a₀ a₁ : Γ ⊢ˣ A)
    → FibStr (Pathˣ A a₀ a₁)
  PathFibStr α a₀ a₁ =
    retractFibStr retract (ExtensionFibStr 𝕚 (α ∘ᶠˢ 𝒑) ∂ _)

  ----------------------------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------------------------

  reindexPathFibStr : {A : Γ → Type ℓ} {α : FibStr A} {a₀ a₁ : Γ ⊢ˣ A}
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
Pathᶠ A a₀ a₁ .fst = Pathˣ (A .fst) a₀ a₁
Pathᶠ A a₀ a₁ .snd = PathFibStr (A .snd) a₀ a₁

opaque
  reindexPathᶠ : {A : Γ ⊢ᶠType ℓ} {a₀ a₁ : Γ ⊢ᶠ A}
    (ρ : Δ → Γ) → Pathᶠ A a₀ a₁ ∘ᶠ ρ ≡ Pathᶠ (A ∘ᶠ ρ) (a₀ ∘ ρ) (a₁ ∘ ρ)
  reindexPathᶠ ρ = Σext refl (reindexPathFibStr ρ)

reflᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠ Pathᶠ A a a
reflᶠ A = refl~ ∘_

------------------------------------------------------------------------------------------
-- Homotopy fiber type
------------------------------------------------------------------------------------------

Fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (b : B) → Type (ℓ ⊔ ℓ')
Fiber f b = Σ a ∈ _ , f a ~ b

Fiberˣ : {A : Γ → Type ℓ} {B : Γ → Type ℓ'} (f : Γ ⊢ˣ A →ˣ B) (b : Γ ⊢ˣ B)
  → (Γ → Type (ℓ ⊔ ℓ'))
Fiberˣ f b γ = Fiber (f γ) (b γ)

opaque
  FiberFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    (f : Γ ⊢ˣ A →ˣ B) (b : Γ ⊢ˣ B)
    → FibStr (Fiberˣ f b)
  FiberFibStr α β f b =
    ΣFibStr α (PathFibStr (β ∘ᶠˢ 𝒑) (uncurry f) (b ∘ 𝒑))

  reindexFiberFibStr : {A : Γ → Type ℓ} {α : FibStr A} {B : Γ → Type ℓ'} {β : FibStr B}
    {f : Γ ⊢ˣ A →ˣ B} {b : Γ ⊢ˣ B}
    (ρ : Δ → Γ)
    → FiberFibStr α β f b ∘ᶠˢ ρ ≡ FiberFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ ρ) (f ∘ ρ) (b ∘ ρ)
  reindexFiberFibStr ρ =
    reindexΣFibStr _ ∙ cong (ΣFibStr _) (reindexPathFibStr _)

Fiberᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') (f : Γ ⊢ᶠ A →ᶠ B) (b : Γ ⊢ᶠ B)
  → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Fiberᶠ A B f b .fst = Fiberˣ f b
Fiberᶠ A B f b .snd = FiberFibStr (A .snd) (B .snd) f b

module _ {A : Type ℓ} {B : Type ℓ'} {f : A → B} where

  opaque
    FiberExt : {b : B} {x y : Fiber f b}
      → x .fst ≡ y .fst → (∀ i → x .snd .at i ≡ y .snd .at i) → x ≡ y
    FiberExt refl p = Σext refl (PathExt p)

  opaque
    FiberExtDep : {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
      → x .fst ≡ y .fst
      → (∀ i → x .snd .at i ≡ y .snd .at i)
      → subst (Fiber f) p x ≡ y
    FiberExtDep refl = FiberExt

  eqToFiber : {b : B} (a : A) → f a ≡ b → Fiber f b
  eqToFiber a eq .fst = a
  eqToFiber a eq .snd = eqToPath eq

  opaque
    fiberPathEq : {b : B} {x y : Fiber f b}
      → x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
    fiberPathEq refl _ = refl

  opaque
    fiberPathEqDep : {b b' : B} (p : b ≡ b')
      {x : Fiber f b} {y : Fiber f b'}
      → subst (Fiber f) p x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
    fiberPathEqDep refl refl _ = refl

  opaque
    fiberDomEqDep : {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
      → subst (Fiber f) p x ≡ y → x .fst ≡ y .fst
    fiberDomEqDep refl refl = refl

------------------------------------------------------------------------------------------
-- Singleton contractibility
------------------------------------------------------------------------------------------

Singl : (A : Type ℓ) (a : A) → Type ℓ
Singl A = Fiber id

Singlᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
Singlᶠ A a = Fiberᶠ A A (λˣ 𝒒) a

singlCenter : {A : Type ℓ} (a : A) → Singl A a
singlCenter a = a , refl~ a

singlCenterᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  → Γ ⊢ᶠ Singlᶠ A a
singlCenterᶠ A a =
  pairᶠ A (Pathᶠ (A ∘ᶠ 𝒑) 𝒒 (a ∘ 𝒑)) a (reflᶠ A a)

opaque
  singlContract : (A : 𝟙 ⊢ᶠType ℓ) (a : A $ᶠ tt) (c : Singlᶠ A (cst a) $ᶠ tt)
    → singlCenter a ~ c
  singlContract A a c = homotopy
    where
    box : (i : 𝕀) → OpenBox 𝕚 (∣ A ∣ ∘ cst tt) 1
    box i .cof = ∂ i
    box i .tube j = ∂-rec i (λ {refl → a}) (λ {refl → c .snd .at j})
    box i .cap .out = a
    box i .cap .out≡ = ∂-elim i (λ {refl → refl}) (λ {refl → c .snd .at1})

    square : (i : 𝕀) → Filler (box i)
    square i = A .snd .lift 𝕚 _ 1 (box i)

    homotopy : (a , refl~ a) ~ c
    homotopy .at i .fst = square i .fill 0 .out
    homotopy .at i .snd = path (λ j → square i .fill j .out) refl (square i .cap≡)
    homotopy .at0 =
      FiberExt
        (sym (square 0 .fill 0 .out≡ (∨l refl)))
        (λ j → sym (square 0 .fill j .out≡ (∨l refl)))
    homotopy .at1 =
      FiberExt
        (sym (square 1 .fill 0 .out≡ (∨r refl)) ∙ c .snd .at0)
        (λ j → sym (square 1 .fill j .out≡ (∨r refl)))

singlContractᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) (c : Γ ⊢ᶠ Singlᶠ A a)
  → Γ ⊢ᶠ Pathᶠ (Singlᶠ A a) (singlCenterᶠ A a) c
singlContractᶠ A a c γ = singlContract (A ∘ᶠ cst γ) (a γ) (c γ)

------------------------------------------------------------------------------------------
-- Transport along paths.
------------------------------------------------------------------------------------------

substᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ') {a₀ a₁ : Γ ⊢ᶠ A}
  (p : Γ ⊢ᶠ Pathᶠ A a₀ a₁)
  → Γ ⊢ᶠ B ∘ᶠ (id ,, a₀)
  → Γ ⊢ᶠ B ∘ᶠ (id ,, a₁)
substᶠ A B p b₀ γ =
  subst (∣ B ∣ ∘ (γ ,_)) (p γ .at1)
    (Transp.transp 𝕚 0 (B ∘ᶠ (cst γ ,, p γ .at))
      (subst (∣ B ∣ ∘ (γ ,_)) (sym (p γ .at0)) (b₀ γ))
      1)

------------------------------------------------------------------------------------------
-- Weak Paulin-Mohring-style J eliminator, stated in a somewhat unorthodox form using
-- singletons for ease of proof.
------------------------------------------------------------------------------------------

Jᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  (P : Γ ▷ᶠ Singlᶠ A a ⊢ᶠType ℓ')
  (d : Γ ⊢ᶠ P ∘ᶠ (id ,, singlCenterᶠ A a))
  (c : Γ ⊢ᶠ Singlᶠ A a)
  → Γ ⊢ᶠ P ∘ᶠ (id ,, c)
Jᶠ A a P d c =
  substᶠ (Singlᶠ A a) P (singlContractᶠ A a c) d
