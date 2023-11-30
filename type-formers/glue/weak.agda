{-

Definition of weak Glue types and their (unaligned) fibrancy.

-}
{-# OPTIONS --rewriting #-}
module type-formers.glue.weak where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.equivs
open import type-formers.paths
open import type-formers.pi

private variable
  ℓ ℓ' ℓ'' : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Glue types
------------------------------------------------------------------------------------------

record Glue (φ : Cof)
  (B : Type ℓ) (A : [ φ ] → Type ℓ)
  (f : (u : [ φ ]) → A u → B) : Type ℓ
  where
  constructor glue
  field
    cod : B
    dom : (u : [ φ ]) → A u
    match : (u : [ φ ]) → f u (dom u) ≡ cod

open Glue public

Glueᴵ : (φ : Γ → Cof)
  (B : Γ → Type ℓ)
  (A : Γ ▷[ φ ] → Type ℓ)
  (f : Γ ▷[ φ ] ⊢ A →ᴵ (B ∘ fst))
  → Γ → Type ℓ
Glueᴵ φ B A f γ = Glue (φ γ) (B γ) (A ∘ (γ ,_)) (f ∘ (γ ,_))

opaque
  GlueExt : {φ : Cof}
    {B : Type ℓ}
    {A : [ φ ] → Type ℓ}
    {f : (u : [ φ ]) → A u → B}
    {g g' : Glue φ B A f}
    (p : ∀ us → g .dom us ≡ g' .dom us)
    (q : g .cod ≡ g' .cod)
    → g ≡ g'
  GlueExt p refl = congΣ (glue _) (funExt p) (funExt' uip')

------------------------------------------------------------------------------------------
-- Isomorphism to the total type
------------------------------------------------------------------------------------------

includeA : (φ : Cof)
  {B : Type ℓ}
  {A : [ φ ] → Type ℓ}
  (f : (u : [ φ ]) → A u → B)
  (u : [ φ ]) → A u → Glue φ B A f
includeA φ f u b .cod = f u b
includeA φ {A = A} f u a .dom v = subst A (cofIsProp' φ) a
includeA φ f u a .match v = sym (congΣ f (cofIsProp' φ) refl)

includeAIso : (φ : Cof)
  {B : Type ℓ}
  {A : [ φ ] → Type ℓ}
  (w : (u : [ φ ]) → A u → B)
  (u : [ φ ]) → A u ≅ Glue φ B A w
includeAIso φ {B} {A} w u = iso
  where
  prfIr : (a : A u) → subst A (cofIsProp φ u u) a ≡ a
  prfIr a = cong (subst A ⦅–⦆ a) uip'

  iso : A u ≅ Glue φ B A w
  iso .to a = includeA φ w u a
  iso .from (glue _ a _) = a u
  iso .inv₁ = funExt prfIr
  iso .inv₂ = funExt fg≡id
    where
    fg≡id : (gl : Glue φ B A w) → (includeA φ w u (gl .dom u)) ≡ gl
    fg≡id gl = GlueExt (substCofEl φ (prfIr _)) (gl .match u)

includeAIsoᴵ : (φ : Γ → Cof)
  {B : Γ → Type ℓ'}
  {A : Γ ▷[ φ ] → Type ℓ'}
  (w : Γ ▷[ φ ] ⊢ A →ᴵ (B ∘ fst))
  → Γ ▷[ φ ] ⊢ A ≅ᴵ (Glueᴵ φ B A w ∘ fst)
includeAIsoᴵ φ w (γ , u) = includeAIso (φ γ) (w ∘ (γ ,_)) u

------------------------------------------------------------------------------------------
-- Fibrancy of Glue types
------------------------------------------------------------------------------------------

module GlueLift {S r φ}
  {B : ⟨ S ⟩ → Type ℓ} (β : FibStr B)
  {A : ⟨ S ⟩ ▷[ φ ] → Type ℓ} (α : FibStr A)
  (fe : ⟨ S ⟩ ▷[ φ ] ⊢ Equivᴵ A (B ∘ fst))
  (box : OpenBox S r (Glueᴵ φ B A (equivFun fe)))
  where

  f = fst ∘ fe
  e = snd ∘ fe

  boxB : OpenBox S r B
  boxB = mapBox (λ _ → cod) box

  fillB = β .lift S r id boxB

  module _ (s : ⟨ S ⟩) where

    module _ (us : [ φ s ]) where

      C₁ = e (s , us) (fillB .fill s .out) .fst
      C₂ = e (s , us) (fillB .fill s .out) .snd

      fiberR : [ box .cof ∨ S ∋ r ≈ s ] → Fiber (f (s , us)) (fillB .fill s .out)
      fiberR =
        ∨-rec (box .cof) (S ∋ r ≈ s)
          (λ v →
            eqToFiber
              (box .tube s v .dom us)
              (box .tube s v .match us ∙ fillB .fill s .out≡ v))
          (λ {refl →
            eqToFiber
              (box .cap .out .dom us)
              (box .cap .out .match us ∙ sym (fillB .cap≡))})
          (λ {v refl →
            congΣ eqToFiber (appCong (cong dom (box .cap .out≡ v))) uip'})

      boxR : OpenBox 𝕚 1 (λ _ → Fiber (f (s , us)) (fillB .fill s .out))
      boxR .cof = box .cof ∨ S ∋ r ≈ s
      boxR .tube k v≡ = C₂ (fiberR v≡) .at k
      boxR .cap .out = C₁
      boxR .cap .out≡ v≡ = C₂ (fiberR v≡) .at1

      fillR =
        Fiberᶠ
          (_ , α ∘ᶠˢ (s ,_))
          (_ , β ∘ᶠˢ (λ _ → s))
          (f ∘ (s ,_))
          (λ _ → fillB .fill s .out)
          .snd .lift 𝕚 1 (λ _ → us) boxR .fill 0

    boxFix : OpenBox 𝕚 1 (λ _ → B s)
    boxFix .cof = box .cof ∨ φ s ∨ S ∋ r ≈ s
    boxFix .tube i =
      ∨-rec (box .cof) (φ s ∨ S ∋ r ≈ s)
        (boxB .tube s)
        (∨-rec (φ s) (S ∋ r ≈ s)
          (λ us → fillR us .out .snd .at i)
          (λ {refl → boxB .cap .out})
          (λ {us refl →
            fiberPathEq (sym (fillR us .out≡ (∨r refl)) ∙ C₂ us (fiberR us (∨r refl)) .at0) i
            ∙ box .cap .out .match us}))
        (λ v →
          ∨-elimEq (φ s) (S ∋ r ≈ s)
            (λ us →
              sym (box .tube s v .match us)
              ∙ fiberPathEq (sym (C₂ us (fiberR us (∨l v)) .at0) ∙ fillR us .out≡ (∨l v)) i)
            (λ {refl → boxB .cap .out≡ v}))
    boxFix .cap .out = fillB .fill s .out
    boxFix .cap .out≡ =
      ∨-elimEq (box .cof) (φ s ∨ S ∋ r ≈ s)
        (λ v → fillB .fill s .out≡ v)
        (∨-elimEq (φ s) (S ∋ r ≈ s)
          (λ us → fillR us .out .snd .at1)
          (λ {refl → sym (fillB .cap≡)}))

    fillFix = β .lift 𝕚 1 (λ _ → s) boxFix .fill 0

  opaque
    filler : Filler box
    filler .fill s .out .dom us = fillR s us .out .fst
    filler .fill s .out .cod = fillFix s .out
    filler .fill s .out .match us =
      sym (fillR s us .out .snd .at0)
      ∙ fillFix s .out≡ (∨r (∨l us))
    filler .fill s .out≡ v =
      GlueExt
        (λ us →
          cong fst (sym (C₂ s us (fiberR s us (∨l v)) .at0))
          ∙ cong fst (fillR s us .out≡ (∨l v)))
        (fillFix s .out≡ (∨l v))
    filler .cap≡ =
      GlueExt
        (λ ur →
          cong fst (sym (fillR r ur .out≡ (∨r refl)))
          ∙ cong fst (C₂ r ur (fiberR r ur (∨r refl)) .at0))
        (sym (fillFix r .out≡ (∨r (∨r refl))))

module GlueVary {S T} (σ : ShapeHom S T) {r φ}
  {B : ⟨ T ⟩ → Type ℓ} (β : FibStr B)
  {A : ⟨ T ⟩ ▷[ φ ] → Type ℓ} (α : FibStr A)
  (fe : ⟨ T ⟩ ▷[ φ ] ⊢ Equivᴵ A (B ∘ fst))
  (box : OpenBox T (⟪ σ ⟫ r) (Glueᴵ φ B A (equivFun fe)))
  where

  module T = GlueLift β α fe box
  module S =
    GlueLift (β ∘ᶠˢ ⟪ σ ⟫) (α ∘ᶠˢ ⟪ σ ⟫ ×id) (fe ∘ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  open T using (f ; e)

  module _ (s : ⟨ S ⟩) where

    varyB : T.fillB .fill (⟪ σ ⟫ s) .out ≡ S.fillB .fill s .out
    varyB = β .vary S T σ r id T.boxB s

    varyC₁ : ∀ uσs → subst (Fiber (f _)) varyB (T.C₁ (⟪ σ ⟫ s) uσs) ≡ S.C₁ s uσs
    varyC₁ uσs = congdep (λ a → e (⟪ σ ⟫ s , uσs) a .fst) varyB

    varyC₂ : ∀ uσs {fib₀ fib₁} (i : 𝕀)
      → subst (Fiber (f _)) varyB fib₀ ≡ fib₁
      → subst (Fiber (f _)) varyB (T.C₂ (⟪ σ ⟫ s) uσs fib₀ .at i) ≡ S.C₂ s uσs fib₁ .at i
    varyC₂ uσs i p =
      congdep₂ (λ a fib → e (_ , uσs) a .snd fib .at i) varyB p

    varyR : ∀ uσs
      → subst (Fiber (f _)) varyB (T.fillR (⟪ σ ⟫ s) uσs .out) ≡ S.fillR s uσs .out
    varyR uσs =
      congdep₂
        (λ b box →
          Fiberᶠ (_ , α ∘ᶠˢ _) (_ , β ∘ᶠˢ _) _ (λ _ → b) .snd .lift 𝕚 1
            (λ _ → uσs) box .fill 0 .out)
        varyB
        (boxExtDep varyB
          (cong (box .cof ∨_) (≈Equivariant σ r s))
          (λ i → takeOutCof (box .cof) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
            (λ u → varyC₂ uσs i (FiberExtDep varyB refl (λ _ → refl)))
            (λ {refl refl → varyC₂ uσs i (FiberExtDep varyB refl (λ _ → refl))}))
          (varyC₁ uσs))

    varyFix : T.fillFix (⟪ σ ⟫ s) .out ≡ S.fillFix s .out
    varyFix =
      cong
        (λ box' → β .lift 𝕚 1 (λ _ → ⟪ σ ⟫ s) box' .fill 0 .out)
        (boxExt
          (cong (λ ψ → box .cof ∨ φ (⟪ σ ⟫ s) ∨ ψ) (≈Equivariant σ r s))
          (λ i → takeOutCof (box .cof)
            (φ (⟪ σ ⟫ s) ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s)
            (φ (⟪ σ ⟫ s) ∨ S ∋ r ≈ s)
            (λ _ → refl)
            (takeOutCof (φ (⟪ σ ⟫ s)) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
              (λ uσs → fiberPathEqDep varyB (varyR uσs) i)
              (λ {refl refl → refl})))
          varyB)

    opaque
      unfolding T.filler S.filler
      eq : T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
      eq = GlueExt (λ uσs → fiberDomEqDep varyB (varyR uσs)) varyFix

opaque
  GlueFibStr : (φ : Γ → Cof)
    {B : Γ → Type ℓ} (β : FibStr B)
    {A : Γ ▷[ φ ] → Type ℓ} (α : FibStr A)
    (fe : Γ ▷[ φ ] ⊢ Equivᴵ A (B ∘ fst))
    → FibStr (Glueᴵ φ B A (equivFun fe))
  GlueFibStr φ β α fe .lift S r p =
    GlueLift.filler (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id) (fe ∘ p ×id)
  GlueFibStr φ β α fe .vary S T σ r p =
    GlueVary.eq σ (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id) (fe ∘ p ×id)

  reindexGlueFibStr : {φ : Γ → Cof}
    {B : Γ → Type ℓ} {β : FibStr B}
    {A : Γ ▷[ φ ] → Type ℓ} {α : FibStr A}
    {fe : Γ ▷[ φ ] ⊢ Equivᴵ A (B ∘ fst)}
    (ρ : Δ → Γ)
    → GlueFibStr φ β α fe ∘ᶠˢ ρ
      ≡ GlueFibStr (φ ∘ ρ) (β ∘ᶠˢ ρ) (α ∘ᶠˢ ρ ×id) (fe ∘ ρ ×id)
  reindexGlueFibStr ρ =
    FibStrExt λ _ _ _ _ _ → GlueExt (λ _ → refl) refl

Glueᶠ : (φ : Γ → Cof)
  (B : Γ ⊢ᶠType ℓ)
  (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
  (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst))
  → Γ ⊢ᶠType ℓ
Glueᶠ φ (B , _) (A , _) fe .fst = Glueᴵ φ B A (equivFun fe)
Glueᶠ φ (_ , β) (_ , α) fe .snd = GlueFibStr φ β α fe

reindexGlueᶠ : {φ : Γ → Cof}
  {B : Γ ⊢ᶠType ℓ}
  {A : Γ ▷[ φ ] ⊢ᶠType ℓ}
  {fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ fst)}
  (ρ : Δ → Γ)
  → Glueᶠ φ B A fe ∘ᶠ ρ ≡ Glueᶠ (φ ∘ ρ) (B ∘ᶠ ρ) (A ∘ᶠ ρ ×id) (fe ∘ ρ ×id)
reindexGlueᶠ ρ = Σext refl (reindexGlueFibStr ρ)
