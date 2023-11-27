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

private variable ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------------------------
-- Glue types
------------------------------------------------------------------------------------------

record Glue (Φ : CofProp)
  (T : [ Φ ] → Type ℓ) (A : Type ℓ)
  (f : (u : [ Φ ]) → T u → A) : Type ℓ
  where
  constructor glue
  field
    dom : (u : [ Φ ]) → T u
    cod : A
    match : (u : [ Φ ]) → f u (dom u) ≡ cod

open Glue public

Glueᴵ : {Γ : Type ℓ}
  (Φ : Γ → CofProp)
  (B : Γ ,[ Φ ] → Type ℓ')
  (A : Γ → Type ℓ')
  (f : Γ ,[ Φ ] ⊢ B →ᴵ (A ∘ fst))
  → Γ → Type ℓ'
Glueᴵ Φ B A f x = Glue (Φ x) (B ∘ (x ,_)) (A x) (f ∘ (x ,_))

opaque
  GlueExt : {Φ : CofProp}
    {B : [ Φ ] → Type ℓ}
    {A : Type ℓ}
    {f : (u : [ Φ ]) → B u → A}
    {g g' : Glue Φ B A f}
    (p : ∀ us → g .dom us ≡ g' .dom us)
    (q : g .cod ≡ g' .cod)
    → g ≡ g'
  GlueExt {g = glue _ a _} p refl =
    cong
      (λ (t , ft≡a) → glue t a ft≡a)
      (Σext (funext p) (funext (λ _ → uipImp)))

------------------------------------------------------------------------------------------
-- Isomorphism to the total type
------------------------------------------------------------------------------------------

includeA : (φ : CofProp)
  {A : [ φ ] → Type ℓ}
  {B : Type ℓ}
  (f : (u : [ φ ]) → A u → B)
  (u : [ φ ]) → A u → Glue φ A B f
includeA φ {A} f u a .dom v = subst A (cofIsProp φ _ _) a
includeA φ f u a .cod = f u a
includeA φ f u a .match v =
  cong (uncurry f) (sym (Σext (cofIsProp φ _ _) refl))

includeAIso : (φ : CofProp)
  {A : [ φ ] → Type ℓ}
  {B : Type ℓ}
  (w : (u : [ φ ]) → A u → B)
  (u : [ φ ]) → A u ≅ Glue φ A B w
includeAIso φ {A} {B} w u = iso
  where
  prfIr : {a : A u} → subst A (cofIsProp φ u u) a ≡ a
  prfIr {a} = cong (λ p → subst A p a) (uip (cofIsProp φ u u) refl)

  iso : A u ≅ Glue φ A B w
  iso .to a = includeA φ w u a
  iso .from (glue a _ _) = a u
  iso .inv₁ = funext (λ a → prfIr)
  iso .inv₂ = funext fg≡id
    where
    parEq : {a a' : (u : [ φ ]) → A u} → a u ≡ a' u → (∀ u' → a u' ≡ a' u')
    parEq {a} {a'} eq u' = subst (λ u' → a u' ≡ a' u') (cofIsProp φ u u') eq

    fg≡id : (gl : Glue φ A B w) → (includeA φ w u (gl .dom u)) ≡ gl
    fg≡id gl = GlueExt (parEq prfIr) (gl .match u)

includeAIsoᴵ : {Γ : Type ℓ} (φ : Γ → CofProp)
  {A : Γ ,[ φ ] → Type ℓ'}
  {B : Γ → Type ℓ'}
  (w : Γ ,[ φ ] ⊢ A →ᴵ (B ∘ fst))
  → Γ ,[ φ ] ⊢ A ≅ᴵ (Glueᴵ φ A B w ∘ fst)
includeAIsoᴵ φ w (γ , u) = includeAIso (φ γ) (w ∘ (γ ,_)) u

------------------------------------------------------------------------------------------
-- Fibrancy of Glue types
------------------------------------------------------------------------------------------

module GlueLift {S r Φ}
  {B : ⟨ S ⟩ ,[ Φ ] → Type ℓ} (β : FibStr B)
  {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A)
  (fe : ⟨ S ⟩ ,[ Φ ] ⊢ Equivᴵ B (A ∘ fst))
  (box : OpenBox S r (Glueᴵ Φ B A (equivFun fe)))
  where

  f = fst ∘ fe
  e = snd ∘ fe

  boxA : OpenBox S r A
  boxA = mapBox (λ _ → cod) box

  fillA = α .lift S r id boxA

  module _ (s : ⟨ S ⟩) where

    module _ (us : [ Φ s ]) where

      C₁ = e (s , us) (fillA .fill s .out) .fst
      C₂ = e (s , us) (fillA .fill s .out) .snd

      fiberR : [ box .cof ∨ S ∋ r ≈ s ] → Fiber (f (s , us)) (fillA .fill s .out)
      fiberR =
        ∨-rec (box .cof) (S ∋ r ≈ s)
          (λ v →
            eqToFiber
              (box .tube v s .dom us)
              (box .tube v s .match us ∙ fillA .fill s .out≡ v))
          (λ {refl →
            eqToFiber
              (box .cap .out .dom us)
              (box .cap .out .match us ∙ sym (fillA .cap≡))})
          (λ {v refl →
            cong (uncurry eqToFiber)
              (Σext (cong (λ g → g .dom us) (box .cap .out≡ v)) uipImp)})

      boxR : OpenBox 𝕚 1 (λ _ → Fiber (f (s , us)) (fillA .fill s .out))
      boxR .cof = box .cof ∨ S ∋ r ≈ s
      boxR .tube v≡ k = C₂ (fiberR v≡) .at k
      boxR .cap .out = C₁
      boxR .cap .out≡ v≡ = C₂ (fiberR v≡) .at1

      fillR =
        FiberFibStr
          (β ∘ᶠˢ (s ,_))
          (α ∘ᶠˢ (λ _ → s))
          (f ∘ (s ,_)) (λ _ → fillA .fill s .out)
          .lift 𝕚 1 (λ _ → us) boxR .fill 0

    boxFix : OpenBox 𝕚 1 (λ _ → A s)
    boxFix .cof = box .cof ∨ Φ s ∨ S ∋ r ≈ s
    boxFix .tube =
      ∨-rec (box .cof) (Φ s ∨ S ∋ r ≈ s)
        (λ v _ → boxA .tube v s)
        (∨-rec (Φ s) (S ∋ r ≈ s)
          (λ us i → fillR us .out .snd .at i)
          (λ {refl _ → boxA .cap .out})
          (λ {us refl → funext λ i →
            fiberPathEq (sym (fillR us .out≡ (∨r refl)) ∙ C₂ us (fiberR us (∨r refl)) .at0) i
            ∙ box .cap .out .match us}))
        (λ v →
          ∨-elimEq (Φ s) (S ∋ r ≈ s)
            (λ us → funext λ i →
              sym (box .tube v s .match us)
              ∙ fiberPathEq (sym (C₂ us (fiberR us (∨l v)) .at0) ∙ fillR us .out≡ (∨l v)) i)
            (λ {refl → funext λ _ → boxA .cap .out≡ v}))
    boxFix .cap .out = fillA .fill s .out
    boxFix .cap .out≡ =
      ∨-elimEq (box .cof) (Φ s ∨ S ∋ r ≈ s)
        (λ v → fillA .fill s .out≡ v)
        (∨-elimEq (Φ s) (S ∋ r ≈ s)
          (λ us → fillR us .out .snd .at1)
          (λ {refl → sym (fillA .cap≡)}))

    fillFix = α .lift 𝕚 1 (λ _ → s) boxFix .fill 0

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

module GlueVary {S T} (σ : ShapeHom S T) {r Φ}
  {B : ⟨ T ⟩ ,[ Φ ] → Type ℓ} (β : FibStr B)
  {A : ⟨ T ⟩ → Type ℓ} (α : FibStr A)
  (fe : ⟨ T ⟩ ,[ Φ ] ⊢ Equivᴵ B (A ∘ fst))
  (box : OpenBox T (⟪ σ ⟫ r) (Glueᴵ Φ B A (equivFun fe)))
  where

  module T = GlueLift β α fe box
  module S =
    GlueLift (β ∘ᶠˢ ⟪ σ ⟫ ×id) (α ∘ᶠˢ ⟪ σ ⟫) (fe ∘ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  open T using (f ; e)

  module _ (s : ⟨ S ⟩) where

    varyA : T.fillA .fill (⟪ σ ⟫ s) .out ≡ S.fillA .fill s .out
    varyA = α .vary S T σ r id T.boxA s

    varyC₁ : ∀ uσs → subst (Fiber (f _)) varyA (T.C₁ (⟪ σ ⟫ s) uσs) ≡ S.C₁ s uσs
    varyC₁ uσs = congdep (λ a → e (⟪ σ ⟫ s , uσs) a .fst) varyA

    varyC₂ : ∀ uσs {fib₀ fib₁} (i : 𝕀)
      → subst (Fiber (f _)) varyA fib₀ ≡ fib₁
      → subst (Fiber (f _)) varyA (T.C₂ (⟪ σ ⟫ s) uσs fib₀ .at i) ≡ S.C₂ s uσs fib₁ .at i
    varyC₂ uσs i p =
      congdep₂ (λ a fib → e (_ , uσs) a .snd fib .at i) varyA p

    varyR : ∀ uσs
      → subst (Fiber (f _)) varyA (T.fillR (⟪ σ ⟫ s) uσs .out) ≡ S.fillR s uσs .out
    varyR uσs =
      congdep₂
        (λ a box →
          FiberFibStr (β ∘ᶠˢ _) (α ∘ᶠˢ _) _ (λ _ → a) .lift 𝕚 1
            (λ _ → uσs) box .fill 0 .out)
        varyA
        (boxExtDep varyA
          (cong (box .cof ∨_) (≈Equivariant σ r s))
          (takeOutCof (box .cof) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
            (λ u → funextDepCod varyA λ i →
              varyC₂ uσs i
                (FiberExtDep varyA refl (λ _ → refl)))
            (λ {refl refl → funextDepCod varyA λ i →
              varyC₂ uσs i
                (FiberExtDep varyA refl (λ _ → refl))}))
          (varyC₁ uσs))

    varyFix : T.fillFix (⟪ σ ⟫ s) .out ≡ S.fillFix s .out
    varyFix =
      cong
        (λ box' → α .lift 𝕚 1 (λ _ → ⟪ σ ⟫ s) box' .fill 0 .out)
        (boxExt
          (cong (λ φ → box .cof ∨ Φ (⟪ σ ⟫ s) ∨ φ) (≈Equivariant σ r s))
          (takeOutCof (box .cof)
            (Φ (⟪ σ ⟫ s) ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s)
            (Φ (⟪ σ ⟫ s) ∨ S ∋ r ≈ s)
            (λ _ → refl)
            (takeOutCof (Φ (⟪ σ ⟫ s)) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
              (λ uσs → funext (fiberPathEqDep varyA (varyR uσs)))
              (λ {refl refl → refl})))
          varyA)

    opaque
      unfolding T.filler S.filler
      eq : T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
      eq = GlueExt (λ uσs → fiberDomEqDep varyA (varyR uσs)) varyFix

opaque
  GlueFibStr : {Γ : Type ℓ}
    (Φ : Γ → CofProp)
    {B : Γ ,[ Φ ] → Type ℓ'} (β : FibStr B)
    {A : Γ → Type ℓ'} (α : FibStr A)
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ B (A ∘ fst))
    → FibStr (Glueᴵ Φ B A (equivFun fe))
  GlueFibStr Φ β α fe .lift S r p =
    GlueLift.filler (β ∘ᶠˢ p ×id) (α ∘ᶠˢ p) (fe ∘ p ×id)
  GlueFibStr Φ β α fe .vary S T σ r p =
    GlueVary.eq σ (β ∘ᶠˢ p ×id) (α ∘ᶠˢ p) (fe ∘ p ×id)

  reindexGlueFibStr : {Δ : Type ℓ} {Γ : Type ℓ'}
    (Φ : Γ → CofProp)
    {B : Γ ,[ Φ ] → Type ℓ''} (β : FibStr B)
    {A : Γ → Type ℓ''} (α : FibStr A)
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ B (A ∘ fst))
    (ρ : Δ → Γ)
    → GlueFibStr Φ β α fe ∘ᶠˢ ρ
      ≡ GlueFibStr (Φ ∘ ρ) (β ∘ᶠˢ ρ ×id) (α ∘ᶠˢ ρ) (fe ∘ ρ ×id)
  reindexGlueFibStr Φ β α fe ρ =
    FibStrExt λ _ _ _ _ _ → GlueExt (λ _ → refl) refl

Glueᶠ : {Γ : Type ℓ}
  (Φ : Γ → CofProp)
  (B : Fib ℓ' (Γ ,[ Φ ]))
  (A : Fib ℓ' Γ)
  (fe : Γ ,[ Φ ] ⊢ Equivᴵ (B .fst) (A .fst ∘ fst))
  → Fib ℓ' Γ
Glueᶠ Φ (B , _) (A , _) fe .fst = Glueᴵ Φ B A (equivFun fe)
Glueᶠ Φ (_ , β) (_ , α) fe .snd = GlueFibStr Φ β α fe

reindexGlueᶠ : {Δ : Type ℓ} {Γ : Type ℓ'}
  (Φ : Γ → CofProp)
  (B : Fib ℓ'' (Γ ,[ Φ ]))
  (A : Fib ℓ'' Γ)
  (fe : Γ ,[ Φ ] ⊢ Equivᴵ (B .fst) (A .fst ∘ fst))
  (ρ : Δ → Γ)
  → Glueᶠ Φ B A fe ∘ᶠ ρ ≡ Glueᶠ (Φ ∘ ρ) (B ∘ᶠ ρ ×id) (A ∘ᶠ ρ) (fe ∘ ρ ×id)
reindexGlueᶠ Φ fe B A ρ = Σext refl (reindexGlueFibStr _ _ _ _ _)
