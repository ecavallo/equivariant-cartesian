{-

Definition of (weak) Glue and their (unaligned) fibrancy.

-}
{-# OPTIONS --rewriting #-}
module glueing.core where

open import prelude
open import shape
open import cofprop
open import fibrations
open import equivs
open import Data.functions
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Glueing
----------------------------------------------------------------------
record Glue (Φ : CofProp)
  (T : [ Φ ] → Set)
  (A : Set)
  (f : (u : [ Φ ]) → T u → A) : Set
  where
  constructor glue
  field
    dom : (u : [ Φ ]) → T u
    cod : A
    match : (u : [ Φ ]) → f u (dom u) ≡ cod

open Glue public

Glue' :
  ∀{a}{Γ : Set a}
  (Φ : Γ → CofProp)
  (B : res Γ Φ → Set)
  (A : Γ → Set)
  (f : (xu : res Γ Φ) → B xu → A (xu .fst))
  → ---------------
  Γ → Set
Glue' Φ B A f x = Glue (Φ x) (λ u → B (x , u)) (A x) (λ u → f (x , u))

glueExt :
  {Φ : CofProp}
  {B : [ Φ ] → Set}
  {A : Set}
  {f : (u : [ Φ ]) → B u → A}
  {g g' : Glue Φ B A f}
  (p : ∀ us → g .dom us ≡ g' .dom us)
  (q : g .cod ≡ g' .cod)
  → ---------------
  g ≡ g'
glueExt {g = glue _ a _} p refl =
  cong
    (λ {(t , ft≡a) → glue t a ft≡a})
    (Σext (funext p) (funext (λ _ → uipImp)))

module FibGlueId
  (S : Shape)
  (Φ : ⟨ S ⟩ → CofProp)
  {B : res ⟨ S ⟩ Φ → Set}
  {A : ⟨ S ⟩ → Set}
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
        FibFiber β (reindex A α fst) .lift
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
    baseFix =
      ( compA .comp s .fst
      , ∨-elimEq ψ (Φ s ∨ S ∋ r ≈ s)
        (λ v → compA .comp s .snd v)
        (∨-elimEq (Φ s) (S ∋ r ≈ s)
          (λ us → compR us .fst .snd .atI)
          (λ {refl → symm (compA .cap)}))
      )

    compFix = α .lift int I (λ _ → s) (ψ ∨ Φ s ∨ S ∋ r ≈ s) tubeFix baseFix .comp O

abstract

  FibGlue : ∀ {ℓ} {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {B : res Γ Φ → Set}
    {A : Γ → Set}
    (fe : Π (Equiv' B (A ∘ fst)))
    → ---------------
    isFib B → isFib A → isFib (Glue' Φ B A (equivFun fe))
  FibGlue Φ {B} {A} fe β α .lift S r p ψ g x₀ =
    record
    { comp = λ s →
      ( glue (λ us → compR s us .fst .fst) (compFix s .fst)
          (λ us → trans
            (compFix s .snd ∣ inr ∣ inl us ∣ ∣)
            (symm (compR s us .fst .snd .atO)))
      , λ v →
        glueExt
          (λ us → trans
            (cong fst (compR s us .snd ∣ inl v ∣))
            (cong fst (symm (C₂ s us (fiberR s us ∣ inl v ∣) .atO))))
          (compFix s .snd ∣ inl v ∣)
      )
    ; cap =
      glueExt
        (λ ur →
          trans
            (cong fst (C₂ r ur (fiberR r ur ∣ inr refl ∣) .atO))
            (cong fst (symm (compR r ur .snd ∣ inr refl ∣))))
        (symm (compFix r .snd ∣ inr ∣ inr refl ∣ ∣))
    }
    where
    open FibGlueId
      S (Φ ∘ p) (fe ∘ p ×id) (reindex B β (p ×id)) (reindex A α p) r ψ g x₀

  FibGlue Φ {B = B} {A = A} fe β α .vary S T σ r p ψ g x₀ s =
    glueExt (λ uσs → fiberDomEqDep varyA (varyR uσs)) varyFix
    where
    module T = FibGlueId
      T (Φ ∘ p) (fe ∘ p ×id)
      (reindex B β (p ×id)) (reindex A α p) (⟪ σ ⟫ r) ψ g x₀
    module S = FibGlueId
      S (Φ ∘ p ∘ ⟪ σ ⟫) (fe ∘ (p ∘ ⟪ σ ⟫) ×id)
      (reindex B β ((p ∘ ⟪ σ ⟫) ×id)) (reindex A α (p ∘ ⟪ σ ⟫)) r ψ (g ◇ ⟪ σ ⟫) x₀

    f = λ su → fe su .fst
    e = λ su → fe su .snd

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
            FibFiber (reindex B β (p ×id)) (reindex A α (p ∘ fst)) .lift int I
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

  reindexGlue : ∀ {ℓ ℓ'}
    {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {B : res Γ Φ → Set}
    {A : Γ → Set}
    (fe : Π (Equiv' B (A ∘ fst)))
    (β : isFib B)
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Glue' Φ B A (equivFun fe)) (FibGlue Φ fe β α) ρ
    ≡ FibGlue (Φ ∘ ρ) (fe ∘ ρ ×id) (reindex B β (ρ ×id)) (reindex A α ρ)
  reindexGlue Φ {B} {A} fe β α ρ =
    fibExt λ _ _ _ _ _ _ _ → glueExt (λ _ → refl) refl
