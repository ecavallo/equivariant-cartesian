{-

Definition of weak Glue types and their (unaligned) fibrancy.

-}
{-# OPTIONS --rewriting #-}
module glueing.weak where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.paths
open import type-formers.equivs

----------------------------------------------------------------------
-- Glueing
----------------------------------------------------------------------
record Glue {ℓ} (Φ : CofProp)
  (T : [ Φ ] → Set ℓ) (A : Set ℓ)
  (f : (u : [ Φ ]) → T u → A) : Set ℓ
  where
  constructor glue
  field
    dom : (u : [ Φ ]) → T u
    cod : A
    match : (u : [ Φ ]) → f u (dom u) ≡ cod

open Glue public

Glue' :
  ∀{ℓ ℓ'} {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (B : Γ ,[ Φ ] → Set ℓ')
  (A : Γ → Set ℓ')
  (f : (xu : Γ ,[ Φ ]) → B xu → A (xu .fst))
  → ---------------
  Γ → Set ℓ'
Glue' Φ B A f x = Glue (Φ x) (λ u → B (x , u)) (A x) (λ u → f (x , u))

opaque
  GlueExt : ∀ {ℓ}
    {Φ : CofProp}
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
      (λ {(t , ft≡a) → glue t a ft≡a})
      (Σext (funext p) (funext (λ _ → uipImp)))

module GlueIsFibId {ℓ}
  {S : Shape}
  {Φ : ⟨ S ⟩ → CofProp}
  {B : ⟨ S ⟩ ,[ Φ ] → Set ℓ}
  {A : ⟨ S ⟩ → Set ℓ}
  (fe : Π (Equiv' B (A ∘ fst)))
  (β : isFib B) (α : isFib A)
  {r : ⟨ S ⟩} (box : OpenBox S r (Glue' Φ B A (equivFun fe)))
  where

  f = λ su → fe su .fst
  e = λ su → fe su .snd

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
              (box .cap .out .match us ∙ symm (fillA .cap≡))})
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
            fiberPathEq (symm (fillR us .out≡ ∣ inr refl ∣) ∙ C₂ us (fiberR us ∣ inr refl ∣) .at0) i
            ∙ box .cap .out .match us}))
        (λ v →
          ∨-elimEq (Φ s) (S ∋ r ≈ s)
            (λ us → funext λ i →
              symm (box .tube v s .match us)
              ∙ fiberPathEq (symm (C₂ us (fiberR us ∣ inl v ∣) .at0) ∙ fillR us .out≡ ∣ inl v ∣) i)
            (λ {refl → funext λ _ → boxA .cap .out≡ v}))
    boxFix .cap .out = fillA .fill s .out
    boxFix .cap .out≡ =
      ∨-elimEq (box .cof) (Φ s ∨ S ∋ r ≈ s)
        (λ v → fillA .fill s .out≡ v)
        (∨-elimEq (Φ s) (S ∋ r ≈ s)
          (λ us → fillR us .out .snd .at1)
          (λ {refl → symm (fillA .cap≡)}))

    fillFix = α .lift 𝕚 1 (λ _ → s) boxFix .fill 0

opaque
  GlueIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {B : Γ ,[ Φ ] → Set ℓ'}
    {A : Γ → Set ℓ'}
    (fe : Π (Equiv' B (A ∘ fst)))
    → ---------------
    isFib B → isFib A → isFib (Glue' Φ B A (equivFun fe))
  GlueIsFib Φ {B} {A} fe β α .lift S r p box = rec
    where
    open GlueIsFibId (fe ∘ p ×id) (reindex β (p ×id)) (reindex α p) box

    rec : Filler box
    rec .fill s .out .dom us = fillR s us .out .fst
    rec .fill s .out .cod = fillFix s .out
    rec .fill s .out .match us =
      symm (fillR s us .out .snd .at0)
      ∙ fillFix s .out≡ ∣ inr ∣ inl us ∣ ∣
    rec .fill s .out≡ v =
      GlueExt
        (λ us →
          cong fst (symm (C₂ s us (fiberR s us ∣ inl v ∣) .at0))
          ∙ cong fst (fillR s us .out≡ ∣ inl v ∣))
        (fillFix s .out≡ ∣ inl v ∣)
    rec .cap≡ =
      GlueExt
        (λ ur →
          cong fst (symm (fillR r ur .out≡ ∣ inr refl ∣))
          ∙ cong fst (C₂ r ur (fiberR r ur ∣ inr refl ∣) .at0))
        (symm (fillFix r .out≡ ∣ inr ∣ inr refl ∣ ∣))

  GlueIsFib {Γ = Γ} Φ {B} {A} fe β α .vary S T σ r p box s =
    GlueExt (λ uσs → fiberDomEqDep varyA (varyR uσs)) varyFix
    where
    module T = GlueIsFibId (fe ∘ p ×id) (reindex β (p ×id)) (reindex α p) box
    module S = GlueIsFibId (fe ∘ (p ∘ ⟪ σ ⟫) ×id)
      (reindex β ((p ∘ ⟪ σ ⟫) ×id)) (reindex α (p ∘ ⟪ σ ⟫)) (reshapeBox σ box)

    f : (γu : Γ ,[ Φ ]) → B γu → A (γu .fst)
    f = fst ∘ fe

    e : (γu : Γ ,[ Φ ]) → IsEquiv (f γu)
    e = snd ∘ fe

    varyA : T.fillA .fill (⟪ σ ⟫ s) .out ≡ S.fillA .fill s .out
    varyA = α .vary S T σ r p T.boxA s

    varyC₁ : ∀ uσs
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.C₁ (⟪ σ ⟫ s) uσs) ≡ S.C₁ s uσs
    varyC₁ uσs = congdep (λ a → e (p (⟪ σ ⟫ s) , uσs) a .fst) varyA

    varyC₂ : ∀ uσs {fib₀ fib₁} (i : 𝕀)
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA fib₀ ≡ fib₁
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.C₂ (⟪ σ ⟫ s) uσs fib₀ .at i)
        ≡ S.C₂ s uσs fib₁ .at i
    varyC₂ uσs i p =
      congdep₂ (λ a fib → e (_ , uσs) a .snd fib .at i) varyA p

    varyR : ∀ uσs
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.fillR (⟪ σ ⟫ s) uσs .out)
        ≡ S.fillR s uσs .out
    varyR uσs =
      congdep₂
        (λ a box →
          FiberIsFib (reindex β (p ×id)) (reindex α (p ∘ fst)) .lift 𝕚 1
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
        (reindexFiber (reindex β (p ×id)) (reindex α (p ∘ fst))
          (λ {(s , uσs) → ⟪ σ ⟫ s , uσs}))

    varyFix : T.fillFix (⟪ σ ⟫ s) .out ≡ S.fillFix s .out
    varyFix =
      cong
        (λ box' → α .lift 𝕚 1 (λ _ → p (⟪ σ ⟫ s)) box' .fill 0 .out)
        (boxExt
          (cong (λ φ → box .cof ∨ Φ (p (⟪ σ ⟫ s)) ∨ φ) (≈Equivariant σ r s))
          (takeOutCof (box .cof) (Φ (p (⟪ σ ⟫ s)) ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (Φ (p (⟪ σ ⟫ s)) ∨ S ∋ r ≈ s)
            (λ _ → refl)
            (takeOutCof (Φ (p (⟪ σ ⟫ s))) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
              (λ uσs → funext (fiberPathEqDep varyA (varyR uσs)))
              (λ {refl refl → refl})))
          varyA)

  reindexGlue : ∀ {ℓ ℓ' ℓ''}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {B : Γ ,[ Φ ] → Set ℓ''}
    {A : Γ → Set ℓ''}
    (fe : Π (Equiv' B (A ∘ fst)))
    (β : isFib B)
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (GlueIsFib Φ fe β α) ρ
    ≡ GlueIsFib (Φ ∘ ρ) (fe ∘ ρ ×id) (reindex β (ρ ×id)) (reindex α ρ)
  reindexGlue Φ fe β α ρ =
    isFibExt λ _ _ _ _ _ → GlueExt (λ _ → refl) refl
