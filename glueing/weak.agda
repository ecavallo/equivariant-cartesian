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

abstract
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
  (S : Shape)
  (Φ : ⟨ S ⟩ → CofProp)
  {B : ⟨ S ⟩ ,[ Φ ] → Set ℓ}
  {A : ⟨ S ⟩ → Set ℓ}
  (fe : Π (Equiv' B (A ∘ fst)))
  (β : isFib B) (α : isFib A)
  (r : ⟨ S ⟩) (ψ : CofProp) (g : [ ψ ] → (s : ⟨ S ⟩) → Glue' Φ B A (equivFun fe) s)
  (x₀ : Glue' Φ B A (equivFun fe) r [ ψ ↦ g ◆ r ])
  where

  f = λ su → fe su .fst
  e = λ su → fe su .snd

  tubeA : [ ψ ] → (s : ⟨ S ⟩) → A s
  tubeA v s = g v s .cod

  baseA : A r [ ψ ↦ tubeA ◆ r ]
  baseA = (x₀ .fst .cod , λ u → cong cod (x₀ .snd u))

  compA = α .lift S r id ψ tubeA baseA

  module _ (s : ⟨ S ⟩) where

    module _ (us : [ Φ s ]) where

      C₁ = e (s , us) (compA .comp s .fst) .fst
      C₂ = e (s , us) (compA .comp s .fst) .snd

      fiberR : [ ψ ∨ S ∋ r ≈ s ] → Fiber (f (s , us)) (compA .comp s .fst)
      fiberR =
        ∨-rec ψ (S ∋ r ≈ s)
          (λ v →
            eqToFiber
              (g v s .dom us)
              (trans (compA .comp s .snd v) (g v s .match us)))
          (λ {refl →
            eqToFiber
              (x₀ .fst .dom us)
              (trans (symm (compA .cap)) (x₀ .fst .match us))})
          (λ {v refl →
            cong (uncurry eqToFiber)
              (Σext (cong (λ g → g .dom us) (x₀ .snd v)) uipImp)})

      tubeR : [ ψ ∨ S ∋ r ≈ s ] → Int → Fiber (f (s , us)) (compA .comp s .fst)
      tubeR v≡ k = C₂ (fiberR v≡) .at k

      baseR : Fiber (f (s , us)) (compA .comp s .fst) [ ψ ∨ S ∋ r ≈ s ↦ tubeR ◆ I ]
      baseR = ( C₁ , λ uv → C₂ (fiberR uv) .atI)

      compR =
        FiberIsFib β (reindex A α fst) .lift
          int I (λ _ → (((s , us) , f (s , us)) , compA .comp s .fst)) (ψ ∨ S ∋ r ≈ s) tubeR baseR .comp O

    tubeFix : [ ψ ∨ Φ s ∨ S ∋ r ≈ s ] → Int → A s
    tubeFix =
      ∨-rec ψ (Φ s ∨ S ∋ r ≈ s)
        (λ v _ → tubeA v s)
        (∨-rec (Φ s) (S ∋ r ≈ s)
          (λ us i → compR us .fst .snd .at i)
          (λ {refl _ → baseA .fst})
          (λ {us refl → funext λ i →
            trans
              (x₀ .fst .match us)
              (fiberPathEq
                (trans
                  (C₂ us (fiberR us ∣ inr refl ∣) .atO)
                  (symm (compR us .snd ∣ inr refl ∣)))
                i)}))
        (λ v →
          ∨-elimEq (Φ s) (S ∋ r ≈ s)
            (λ us → funext λ i →
              trans
                (fiberPathEq
                  (trans
                    (compR us .snd ∣ inl v ∣)
                    (symm (C₂ us (fiberR us ∣ inl v ∣) .atO)))
                  i)
                (symm (g v s .match us)))
            (λ {refl → funext λ _ → baseA .snd v}))

    baseFix : A s [ ψ ∨ Φ s ∨ S ∋ r ≈ s ↦ tubeFix ◆ I ]
    baseFix .fst = compA .comp s .fst
    baseFix .snd =
      ∨-elimEq ψ (Φ s ∨ S ∋ r ≈ s)
        (λ v → compA .comp s .snd v)
        (∨-elimEq (Φ s) (S ∋ r ≈ s)
          (λ us → compR us .fst .snd .atI)
          (λ {refl → symm (compA .cap)}))

    compFix = α .lift int I (λ _ → s) (ψ ∨ Φ s ∨ S ∋ r ≈ s) tubeFix baseFix .comp O

abstract
  GlueIsFib : ∀ {ℓ ℓ'} {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {B : Γ ,[ Φ ] → Set ℓ'}
    {A : Γ → Set ℓ'}
    (fe : Π (Equiv' B (A ∘ fst)))
    → ---------------
    isFib B → isFib A → isFib (Glue' Φ B A (equivFun fe))
  GlueIsFib Φ {B} {A} fe β α .lift S r p ψ g x₀ = rec
    where
    open GlueIsFibId
      S (Φ ∘ p) (fe ∘ p ×id) (reindex B β (p ×id)) (reindex A α p) r ψ g x₀

    rec : Comp S r _ ψ g x₀
    rec .comp s .fst .dom us = compR s us .fst .fst
    rec .comp s .fst .cod = compFix s .fst
    rec .comp s .fst .match us =
      trans
        (compFix s .snd ∣ inr ∣ inl us ∣ ∣)
        (symm (compR s us .fst .snd .atO))
    rec .comp s .snd v =
      GlueExt
        (λ us → trans
          (cong fst (compR s us .snd ∣ inl v ∣))
          (cong fst (symm (C₂ s us (fiberR s us ∣ inl v ∣) .atO))))
        (compFix s .snd ∣ inl v ∣)
    rec .cap =
      GlueExt
        (λ ur →
          trans
            (cong fst (C₂ r ur (fiberR r ur ∣ inr refl ∣) .atO))
            (cong fst (symm (compR r ur .snd ∣ inr refl ∣))))
        (symm (compFix r .snd ∣ inr ∣ inr refl ∣ ∣))

  GlueIsFib {Γ = Γ} Φ {B} {A} fe β α .vary S T σ r p ψ g x₀ s =
    GlueExt (λ uσs → fiberDomEqDep varyA (varyR uσs)) varyFix
    where
    module T = GlueIsFibId
      T (Φ ∘ p) (fe ∘ p ×id)
      (reindex B β (p ×id)) (reindex A α p) (⟪ σ ⟫ r) ψ g x₀
    module S = GlueIsFibId
      S (Φ ∘ p ∘ ⟪ σ ⟫) (fe ∘ (p ∘ ⟪ σ ⟫) ×id)
      (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) (reindex A α (p ∘ ⟪ σ ⟫)) r ψ (g ◇ ⟪ σ ⟫) x₀

    f : (γu : Γ ,[ Φ ]) → B γu → A (γu .fst)
    f = fst ∘ fe

    e : (γu : Γ ,[ Φ ]) → IsEquiv (f γu)
    e = snd ∘ fe

    varyA : T.compA .comp (⟪ σ ⟫ s) .fst ≡ S.compA .comp s .fst
    varyA = α .vary S T σ r p ψ T.tubeA T.baseA s

    varyC₁ : ∀ uσs
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.C₁ (⟪ σ ⟫ s) uσs) ≡ S.C₁ s uσs
    varyC₁ uσs = congdep (λ a → e (p (⟪ σ ⟫ s) , uσs) a .fst) varyA

    varyC₂ : ∀ uσs {fib₀ fib₁} (i : Int)
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA fib₀ ≡ fib₁
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.C₂ (⟪ σ ⟫ s) uσs fib₀ .at i)
        ≡ S.C₂ s uσs fib₁ .at i
    varyC₂ uσs i p =
      congdep₂ (λ a fib → e (_ , uσs) a .snd fib .at i) varyA p

    varyR : ∀ uσs
      → subst (curry (Fiber' B (A ∘ fst)) ((_ , uσs) , _)) varyA (T.compR (⟪ σ ⟫ s) uσs .fst)
        ≡ S.compR s uσs .fst
    varyR uσs =
      trans
        (cong
          (λ δ →
            δ .lift int I (λ _ → (((s , uσs) , _) , _)) _
              (S.tubeR _ uσs) (S.baseR _ uσs) .comp O .fst)
          (reindexFiber (reindex B β (p ×id)) (reindex A α (p ∘ fst))
            (λ {(s , uσs) → ⟪ σ ⟫ s , uσs})))
        (congdep₂
          (λ {a (φ' , g' , x') →
            FiberIsFib (reindex B β (p ×id)) (reindex A α (p ∘ fst)) .lift int I
              (λ _ → (((_ , uσs) , _) , a)) φ' g' x' .comp O .fst})
          varyA
          (boxEqDep int varyA
            (cong (λ φ' → ψ ∨ φ') (≈Equivariant σ r s))
            (takeOutCof ψ (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
              (λ u → funextDepCod varyA λ i →
                varyC₂ uσs i
                  (FiberExtDep varyA refl (λ _ → refl)))
              (λ {refl refl → funextDepCod varyA λ i →
                varyC₂ uσs i
                  (FiberExtDep varyA refl (λ _ → refl))}))
            I
            (varyC₁ uσs)))

    varyFix : T.compFix (⟪ σ ⟫ s) .fst ≡ S.compFix s .fst
    varyFix =
      cong
        (λ {(φ' , g' , x') → α .lift int I (λ _ → p (⟪ σ ⟫ s)) φ' g' x' .comp O .fst})
        (boxEq int
          (cong (λ φ' → ψ ∨ Φ (p (⟪ σ ⟫ s)) ∨ φ') (≈Equivariant σ r s))
          (takeOutCof ψ (Φ (p (⟪ σ ⟫ s)) ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (Φ (p (⟪ σ ⟫ s)) ∨ S ∋ r ≈ s)
            (λ v → refl)
            (takeOutCof (Φ (p (⟪ σ ⟫ s))) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
              (λ uσs → funext (fiberPathEqDep varyA (varyR uσs)))
              (λ {refl refl → refl})))
          I
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
    reindex (Glue' Φ B A (equivFun fe)) (GlueIsFib Φ fe β α) ρ
    ≡ GlueIsFib (Φ ∘ ρ) (fe ∘ ρ ×id) (reindex B β (ρ ×id)) (reindex A α ρ)
  reindexGlue Φ {B} {A} fe β α ρ =
    isFibExt λ _ _ _ _ _ _ _ → GlueExt (λ _ → refl) refl
