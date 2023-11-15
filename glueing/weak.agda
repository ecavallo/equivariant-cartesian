{-

Definition of weak Glue types and their (unaligned) fibrancy.

-}
{-# OPTIONS --rewriting #-}
module glueing.weak where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.equivs
open import type-formers.paths
open import type-formers.pi

private variable ℓ ℓ' ℓ'' : Level

----------------------------------------------------------------------
-- Glueing
----------------------------------------------------------------------
record Glue (Φ : CofProp)
  (T : [ Φ ] → Set ℓ) (A : Set ℓ)
  (f : (u : [ Φ ]) → T u → A) : Set ℓ
  where
  constructor glue
  field
    dom : (u : [ Φ ]) → T u
    cod : A
    match : (u : [ Φ ]) → f u (dom u) ≡ cod

open Glue public

Glueᴵ : {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (B : Γ ,[ Φ ] → Set ℓ')
  (A : Γ → Set ℓ')
  (f : Π (B →ᴵ (A ∘ fst)))
  → ---------------
  Γ → Set ℓ'
Glueᴵ Φ B A f x = Glue (Φ x) (B ∘ (x ,_)) (A x) (f ∘ (x ,_))

opaque
  GlueExt : {Φ : CofProp}
    {B : [ Φ ] → Set ℓ}
    {A : Set ℓ}
    {f : (u : [ Φ ]) → B u → A}
    {g g' : Glue Φ B A f}
    (p : ∀ us → g .dom us ≡ g' .dom us)
    (q : g .cod ≡ g' .cod)
    → ---------------
    g ≡ g'
  GlueExt {g = glue _ a _} p refl =
    cong
      (λ (t , ft≡a) → glue t a ft≡a)
      (Σext (funext p) (funext (λ _ → uipImp)))

module GlueLift {S r Φ}
  {B : ⟨ S ⟩ ,[ Φ ] → Set ℓ}
  {A : ⟨ S ⟩ → Set ℓ}
  (fe : Π (Equivᴵ B (A ∘ fst)))
  (β : isFib B) (α : isFib A)
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
        FiberIsFib β (reindex α fst) .lift
          𝕚 1 (λ _ → (((s , us) , f (s , us)) , fillA .fill s .out)) boxR .fill 0

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
  {B : ⟨ T ⟩ ,[ Φ ] → Set ℓ}
  {A : ⟨ T ⟩ → Set ℓ}
  (fe : Π (Equivᴵ B (A ∘ fst)))
  (β : isFib B) (α : isFib A)
  (box : OpenBox T (⟪ σ ⟫ r) (Glueᴵ Φ B A (equivFun fe)))
  where

  module T = GlueLift fe β α box
  module S =
    GlueLift (fe ∘ (⟪ σ ⟫ ×id))
      (reindex β (⟪ σ ⟫ ×id)) (reindex α ⟪ σ ⟫) (reshapeBox σ box)

  open T using (f ; e)

  module _ (s : ⟨ S ⟩) where

    varyA : T.fillA .fill (⟪ σ ⟫ s) .out ≡ S.fillA .fill s .out
    varyA = α .vary S T σ r id T.boxA s

    varyC₁ : ∀ uσs
      → subst (curry (Fiberᴵ B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.C₁ (⟪ σ ⟫ s) uσs) ≡ S.C₁ s uσs
    varyC₁ uσs = congdep (λ a → e (⟪ σ ⟫ s , uσs) a .fst) varyA

    varyC₂ : ∀ uσs {fib₀ fib₁} (i : 𝕀)
      → subst (curry (Fiberᴵ B (A ∘ fst)) ((_ , uσs) , _)) varyA fib₀ ≡ fib₁
      → subst (curry (Fiberᴵ B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.C₂ (⟪ σ ⟫ s) uσs fib₀ .at i)
        ≡ S.C₂ s uσs fib₁ .at i
    varyC₂ uσs i p =
      congdep₂ (λ a fib → e (_ , uσs) a .snd fib .at i) varyA p

    varyR : ∀ uσs
      → subst (curry (Fiberᴵ B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.fillR (⟪ σ ⟫ s) uσs .out)
        ≡ S.fillR s uσs .out
    varyR uσs =
      congdep₂
        (λ a box →
          FiberIsFib β (reindex α fst) .lift 𝕚 1
            (λ _ → (((_ , uσs) , _) , a)) box .fill 0 .out)
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
      ∙
      cong
        (λ δ → δ .lift 𝕚 1 (λ _ → (((s , uσs) , _) , _)) (S.boxR _ uσs) .fill 0 .out)
        (reindexFiber β (reindex α fst) (⟪ σ ⟫ ×id))

    varyFix : T.fillFix (⟪ σ ⟫ s) .out ≡ S.fillFix s .out
    varyFix =
      cong
        (λ box' → α .lift 𝕚 1 (λ _ → ⟪ σ ⟫ s) box' .fill 0 .out)
        (boxExt
          (cong (λ φ → box .cof ∨ Φ (⟪ σ ⟫ s) ∨ φ) (≈Equivariant σ r s))
          (takeOutCof (box .cof) (Φ (⟪ σ ⟫ s) ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (Φ (⟪ σ ⟫ s) ∨ S ∋ r ≈ s)
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
  GlueIsFib : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {B : Γ ,[ Φ ] → Set ℓ'}
    {A : Γ → Set ℓ'}
    (fe : Π (Equivᴵ B (A ∘ fst)))
    → ---------------
    isFib B → isFib A → isFib (Glueᴵ Φ B A (equivFun fe))
  GlueIsFib Φ fe β α .lift S r p =
    GlueLift.filler (fe ∘ p ×id) (reindex β (p ×id)) (reindex α p)
  GlueIsFib Φ fe β α .vary S T σ r p =
    GlueVary.eq σ (fe ∘ p ×id) (reindex β (p ×id)) (reindex α p)

opaque
  unfolding GlueIsFib
  reindexGlue : {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {B : Γ ,[ Φ ] → Set ℓ''}
    {A : Γ → Set ℓ''}
    (fe : Π (Equivᴵ B (A ∘ fst)))
    (β : isFib B)
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (GlueIsFib Φ fe β α) ρ
    ≡ GlueIsFib (Φ ∘ ρ) (fe ∘ ρ ×id) (reindex β (ρ ×id)) (reindex α ρ)
  reindexGlue Φ fe β α ρ =
    isFibExt λ _ _ _ _ _ → GlueExt (λ _ → refl) refl
