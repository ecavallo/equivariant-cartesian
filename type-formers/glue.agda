{-

Definition of glue types and proof of fibrancy.

We first define fibrant "weak" glue types (which align with the domain of the partial
equivalence only up to isomorphism), then use realignment for fibrations to construct
true ("strict") glue types.

-}
{-# OPTIONS --rewriting #-}
module type-formers.glue where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.realignment
open import fibration.trivial
open import type-formers.equivs
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma

private variable
  ℓ ℓ' ℓ'' : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Weak Glue types
------------------------------------------------------------------------------------------

record WeakGlue (φ : Cof)
  {B : Type ℓ} {A : [ φ ] → Type ℓ}
  (f : (u : [ φ ]) → A u → B) : Type ℓ
  where
  constructor wglue
  field
    cod : B
    dom : (u : [ φ ]) → A u
    match : (u : [ φ ]) → f u (dom u) ≡ cod

open WeakGlue public

WeakGlueᴵ : (φ : Γ → Cof)
  {B : Γ → Type ℓ}
  {A : Γ ▷[ φ ] → Type ℓ}
  (f : Γ ▷[ φ ] ⊢ A →ᴵ (B ∘ wk[ φ ]))
  → Γ → Type ℓ
WeakGlueᴵ φ f γ = WeakGlue (φ γ) (f ∘ (γ ,_))

opaque
  WeakGlueExt : {φ : Cof}
    {B : Type ℓ}
    {A : [ φ ] → Type ℓ}
    {f : (u : [ φ ]) → A u → B}
    {g g' : WeakGlue φ f}
    (p : ∀ us → g .dom us ≡ g' .dom us)
    (q : g .cod ≡ g' .cod)
    → g ≡ g'
  WeakGlueExt p refl = congΣ (wglue _) (funExt p) (funExt' uip')

------------------------------------------------------------------------------------------
-- Partial isomorphism from the domain
------------------------------------------------------------------------------------------

domToGlue : (φ : Cof)
  {B : Type ℓ}
  {A : [ φ ] → Type ℓ}
  (f : (u : [ φ ]) → A u → B)
  (u : [ φ ]) → A u → WeakGlue φ f
domToGlue φ f u b .cod = f u b
domToGlue φ {A = A} f u a .dom v = subst A (cofIsProp' φ) a
domToGlue φ f u a .match v = sym (congΣ f (cofIsProp' φ) refl)

domIsoGlue : (φ : Cof)
  {B : Type ℓ}
  {A : [ φ ] → Type ℓ}
  (w : (u : [ φ ]) → A u → B)
  (u : [ φ ]) → A u ≅ WeakGlue φ w
domIsoGlue φ {B} {A} w u = iso
  where
  prfIr : (a : A u) → subst A (cofIsProp φ u u) a ≡ a
  prfIr a = cong (subst A ⦅–⦆ a) uip'

  iso : A u ≅ WeakGlue φ w
  iso .to a = domToGlue φ w u a
  iso .from (wglue _ a _) = a u
  iso .inv₁ = funExt prfIr
  iso .inv₂ = funExt fg≡id
    where
    fg≡id : (gl : WeakGlue φ w) → (domToGlue φ w u (gl .dom u)) ≡ gl
    fg≡id gl = WeakGlueExt (substCofEl φ (prfIr _)) (gl .match u)

domIsoGlueᴵ : (φ : Γ → Cof)
  {B : Γ → Type ℓ'}
  {A : Γ ▷[ φ ] → Type ℓ'}
  (w : Γ ▷[ φ ] ⊢ A →ᴵ (B ∘ wk[ φ ]))
  → Γ ▷[ φ ] ⊢ A ≅ᴵ (WeakGlueᴵ φ w ∘ wk[ φ ])
domIsoGlueᴵ φ w (γ , u) = domIsoGlue (φ γ) (w ∘ (γ ,_)) u

------------------------------------------------------------------------------------------
-- Fibrancy of weak Glue types
------------------------------------------------------------------------------------------

module WeakGlueLift {S r φ}
  {B : ⟨ S ⟩ → Type ℓ} (β : FibStr B)
  {A : ⟨ S ⟩ ▷[ φ ] → Type ℓ} (α : FibStr A)
  (fe : ⟨ S ⟩ ▷[ φ ] ⊢ Equivᴵ A (B ∘ wk[ φ ]))
  (box : OpenBox S r (WeakGlueᴵ φ (fstᴵ fe)))
  where

  private
    f = fst ∘ fe
    e = snd ∘ fe

  codBox : OpenBox S r B
  codBox = mapBox (λ _ → cod) box

  codFill = β .lift S r id codBox

  module _ (s : ⟨ S ⟩) where

    module _ (us : [ φ s ]) where

      center = e (s , us) (codFill .fill s .out) .fst
      contractor = e (s , us) (codFill .fill s .out) .snd

      partialFiber : [ box .cof ∨ S ∋ r ≈ s ] → Fiber (f (s , us)) (codFill .fill s .out)
      partialFiber =
        ∨-rec (box .cof) (S ∋ r ≈ s)
          (λ v →
            eqToFiber
              (box .tube s v .dom us)
              (box .tube s v .match us ∙ codFill .fill s .out≡ v))
          (λ {refl →
            eqToFiber
              (box .cap .out .dom us)
              (box .cap .out .match us ∙ sym (codFill .cap≡))})
          (λ {v refl →
            congΣ eqToFiber (appCong (cong dom (box .cap .out≡ v))) uip'})

      fiberBox : OpenBox 𝕚 1 (cst (Fiber (f (s , us)) (codFill .fill s .out)))
      fiberBox .cof = box .cof ∨ S ∋ r ≈ s
      fiberBox .tube k v≡ = contractor (partialFiber v≡) .at k
      fiberBox .cap .out = center
      fiberBox .cap .out≡ v≡ = contractor (partialFiber v≡) .at1

      fiberFill =
        Fiberᶠ
          (_ , α ∘ᶠˢ (s ,_))
          (_ , β ∘ᶠˢ (cst s))
          (f ∘ (s ,_))
          (cst (codFill .fill s .out))
          .snd .lift 𝕚 1 (cst us) fiberBox .fill 0

    codFixBox : OpenBox 𝕚 1 (cst (B s))
    codFixBox .cof = box .cof ∨ φ s ∨ S ∋ r ≈ s
    codFixBox .tube i =
      ∨-rec (box .cof) (φ s ∨ S ∋ r ≈ s)
        (codBox .tube s)
        (∨-rec (φ s) (S ∋ r ≈ s)
          (λ us → fiberFill us .out .snd .at i)
          (λ {refl → codBox .cap .out})
          (λ {us refl →
            fiberPathEq
              (sym (fiberFill us .out≡ (∨r refl))
                ∙ contractor us (partialFiber us (∨r refl)) .at0)
              i
            ∙ box .cap .out .match us}))
        (λ v →
          ∨-elimEq (φ s) (S ∋ r ≈ s)
            (λ us →
              sym (box .tube s v .match us)
              ∙ fiberPathEq
                  (sym (contractor us (partialFiber us (∨l v)) .at0)
                    ∙ fiberFill us .out≡ (∨l v)) i)
            (λ {refl → codBox .cap .out≡ v}))
    codFixBox .cap .out = codFill .fill s .out
    codFixBox .cap .out≡ =
      ∨-elimEq (box .cof) (φ s ∨ S ∋ r ≈ s)
        (λ v → codFill .fill s .out≡ v)
        (∨-elimEq (φ s) (S ∋ r ≈ s)
          (λ us → fiberFill us .out .snd .at1)
          (λ {refl → sym (codFill .cap≡)}))

    codFixFill = β .lift 𝕚 1 (cst s) codFixBox .fill 0

  opaque
    filler : Filler box
    filler .fill s .out .dom us = fiberFill s us .out .fst
    filler .fill s .out .cod = codFixFill s .out
    filler .fill s .out .match us =
      sym (fiberFill s us .out .snd .at0)
      ∙ codFixFill s .out≡ (∨r (∨l us))
    filler .fill s .out≡ v =
      WeakGlueExt
        (λ us →
          cong fst (sym (contractor s us (partialFiber s us (∨l v)) .at0))
          ∙ cong fst (fiberFill s us .out≡ (∨l v)))
        (codFixFill s .out≡ (∨l v))
    filler .cap≡ =
      WeakGlueExt
        (λ ur →
          cong fst (sym (fiberFill r ur .out≡ (∨r refl)))
          ∙ cong fst (contractor r ur (partialFiber r ur (∨r refl)) .at0))
        (sym (codFixFill r .out≡ (∨r (∨r refl))))

module WeakGlueVary {S T} (σ : ShapeHom S T) {r φ}
  {B : ⟨ T ⟩ → Type ℓ} (β : FibStr B)
  {A : ⟨ T ⟩ ▷[ φ ] → Type ℓ} (α : FibStr A)
  (fe : ⟨ T ⟩ ▷[ φ ] ⊢ Equivᴵ A (B ∘ wk[ φ ]))
  (box : OpenBox T (⟪ σ ⟫ r) (WeakGlueᴵ φ (fstᴵ fe)))
  where

  module T = WeakGlueLift β α fe box
  module S =
    WeakGlueLift (β ∘ᶠˢ ⟪ σ ⟫) (α ∘ᶠˢ ⟪ σ ⟫ ×id) (fe ∘ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  private
    f = fst ∘ fe
    e = snd ∘ fe

  module _ (s : ⟨ S ⟩) where

    varyCod : T.codFill .fill (⟪ σ ⟫ s) .out ≡ S.codFill .fill s .out
    varyCod = β .vary S T σ r id T.codBox s

    varyCenter : ∀ uσs
      → subst (Fiber (f _)) varyCod (T.center (⟪ σ ⟫ s) uσs) ≡ S.center s uσs
    varyCenter uσs = congdep (λ a → e (⟪ σ ⟫ s , uσs) a .fst) varyCod

    varyContractor : ∀ uσs {fib₀ fib₁} (i : 𝕀)
      → subst (Fiber (f _)) varyCod fib₀ ≡ fib₁
      → subst (Fiber (f _)) varyCod (T.contractor (⟪ σ ⟫ s) uσs fib₀ .at i)
        ≡ S.contractor s uσs fib₁ .at i
    varyContractor uσs i p =
      congdep₂ (λ a fib → e (_ , uσs) a .snd fib .at i) varyCod p

    varyFiber : ∀ uσs
      → subst (Fiber (f _)) varyCod (T.fiberFill (⟪ σ ⟫ s) uσs .out)
        ≡ S.fiberFill s uσs .out
    varyFiber uσs =
      congdep₂
        (λ b box →
          Fiberᶠ (_ , α ∘ᶠˢ _) (_ , β ∘ᶠˢ _) _ (cst b) .snd .lift _ _
            (cst uσs) box .fill 0 .out)
        varyCod
        (boxExtDep varyCod
          (cong (box .cof ∨_) (≈Equivariant σ r s))
          (λ i → takeOutCof (box .cof) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
            (λ u → varyContractor uσs i (FiberExtDep varyCod refl (cst refl)))
            (λ {refl refl → varyContractor uσs i (FiberExtDep varyCod refl (cst refl))}))
          (varyCenter uσs))

    varyCodFix : T.codFixFill (⟪ σ ⟫ s) .out ≡ S.codFixFill s .out
    varyCodFix =
      cong
        (λ box' → β .lift 𝕚 1 (cst (⟪ σ ⟫ s)) box' .fill 0 .out)
        (boxExt
          (cong (λ ψ → box .cof ∨ φ (⟪ σ ⟫ s) ∨ ψ) (≈Equivariant σ r s))
          (λ i → takeOutCof (box .cof)
            (φ (⟪ σ ⟫ s) ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s)
            (φ (⟪ σ ⟫ s) ∨ S ∋ r ≈ s)
            (λ _ → refl)
            (takeOutCof (φ (⟪ σ ⟫ s)) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
              (λ uσs → fiberPathEqDep varyCod (varyFiber uσs) i)
              (λ {refl refl → refl})))
          varyCod)

    opaque
      unfolding T.filler S.filler
      eq : T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
      eq = WeakGlueExt (λ uσs → fiberDomEqDep varyCod (varyFiber uσs)) varyCodFix

opaque
  WeakGlueFibStr : (φ : Γ → Cof)
    {B : Γ → Type ℓ} (β : FibStr B)
    {A : Γ ▷[ φ ] → Type ℓ} (α : FibStr A)
    (fe : Γ ▷[ φ ] ⊢ Equivᴵ A (B ∘ wk[ φ ]))
    → FibStr (WeakGlueᴵ φ (fstᴵ fe))
  WeakGlueFibStr φ β α fe .lift S r p =
    WeakGlueLift.filler (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id) (fe ∘ p ×id)
  WeakGlueFibStr φ β α fe .vary S T σ r p =
    WeakGlueVary.eq σ (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id) (fe ∘ p ×id)

  reindexWeakGlueFibStr : {φ : Γ → Cof}
    {B : Γ → Type ℓ} {β : FibStr B}
    {A : Γ ▷[ φ ] → Type ℓ} {α : FibStr A}
    {fe : Γ ▷[ φ ] ⊢ Equivᴵ A (B ∘ wk[ φ ])}
    (ρ : Δ → Γ)
    → WeakGlueFibStr φ β α fe ∘ᶠˢ ρ
      ≡ WeakGlueFibStr (φ ∘ ρ) (β ∘ᶠˢ ρ) (α ∘ᶠˢ ρ ×id) (fe ∘ ρ ×id)
  reindexWeakGlueFibStr ρ =
    FibStrExt λ _ _ _ _ _ → WeakGlueExt (λ _ → refl) refl

WeakGlueᶠ : (φ : Γ → Cof)
  (B : Γ ⊢ᶠType ℓ)
  (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
  (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ]))
  → Γ ⊢ᶠType ℓ
WeakGlueᶠ φ (B , _) (A , _) fe .fst = WeakGlueᴵ φ (fstᴵ fe)
WeakGlueᶠ φ (_ , β) (_ , α) fe .snd = WeakGlueFibStr φ β α fe

reindexWeakGlueᶠ : {φ : Γ → Cof}
  {B : Γ ⊢ᶠType ℓ}
  {A : Γ ▷[ φ ] ⊢ᶠType ℓ}
  {fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ])}
  (ρ : Δ → Γ)
  → WeakGlueᶠ φ B A fe ∘ᶠ ρ ≡ WeakGlueᶠ (φ ∘ ρ) (B ∘ᶠ ρ) (A ∘ᶠ ρ ×id) (fe ∘ ρ ×id)
reindexWeakGlueᶠ ρ = Σext refl (reindexWeakGlueFibStr ρ)

------------------------------------------------------------------------------------------
-- Equivalence to the codomain for weak Glue types
------------------------------------------------------------------------------------------

unglueᶠ : (φ : Γ → Cof)
  (B : Γ ⊢ᶠType ℓ)
  (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
  (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ]))
  → Γ ⊢ᶠ WeakGlueᶠ φ B A fe →ᶠ B
unglueᶠ φ B A fe _ = cod

unglueFiberTFibStr : (φ : Γ → Cof)
  (B : Γ ⊢ᶠType ℓ)
  (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
  (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ]))
  → TFibStr (Fiberᴵ (unglueᶠ φ B A fe ∘ fst) snd)
unglueFiberTFibStr φ B A fe (γ , b) ψ unglueFiber = ext
  where
  fFiber : (u : [ φ γ ]) → [ ψ ] → Fiber (fe (γ , u) .fst) b
  fFiber u v .fst = unglueFiber v .fst .dom u
  fFiber u v .snd =
    subst (_~ b) (sym (unglueFiber v .fst .match u)) (unglueFiber v .snd)

  extFFiber : (u : [ φ γ ]) → Fiber (fe (γ , u) .fst) b [ ψ ↦ fFiber u ]
  extFFiber u = equivToFiberTFib A (B ∘ᶠ fst) fe _ _ (fFiber u)

  codBox : OpenBox 𝕚 1 (cst (B .fst γ))
  codBox .cof = φ γ ∨ ψ
  codBox .tube i =
    ∨-rec (φ γ) ψ
      (λ u → extFFiber u .out .snd .at i)
      (λ v → unglueFiber v .snd .at i)
      (λ u v →
        sym (cong (at ⦅–⦆ i ∘ snd) (extFFiber u .out≡ v))
        ∙ substNaturality (λ _ → at ⦅–⦆ i) (sym (unglueFiber v .fst .match u))
        ∙ substConst (sym (unglueFiber v .fst .match u)) _)
  codBox .cap .out = b
  codBox .cap .out≡ =
    ∨-elimEq (φ γ) ψ
      (λ u → extFFiber u .out .snd .at1)
      (λ v → unglueFiber v .snd .at1)

  codFiller : Filler codBox
  codFiller = B .snd .lift _ _ _ codBox

  ext : Fiber cod b [ ψ ↦ unglueFiber ]
  ext .out .fst .cod = codFiller .fill 0 .out
  ext .out .fst .dom u = extFFiber u .out .fst
  ext .out .fst .match u =
    sym (extFFiber u .out .snd .at0) ∙ codFiller .fill 0 .out≡ (∨l u)
  ext .out .snd .at i = codFiller .fill i .out
  ext .out .snd .at0 = refl
  ext .out .snd .at1 = codFiller .cap≡
  ext .out≡ v =
    FiberExt
      (WeakGlueExt
        (λ u → cong fst (extFFiber u .out≡ v))
        (sym (unglueFiber v .snd .at0) ∙ codFiller .fill 0 .out≡ (∨r v)))
      (λ i → codFiller .fill i .out≡ (∨r v))

unglueIsEquiv : (φ : Γ → Cof)
  (B : Γ ⊢ᶠType ℓ)
  (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
  (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ]))
  → Γ ⊢ᶠ IsEquivᶠ (WeakGlueᶠ φ B A fe) B (unglueᶠ φ B A fe)
unglueIsEquiv φ B A fe =
  fiberTFibToIsEquiv (WeakGlueᶠ φ B A fe) B (unglueFiberTFibStr φ B A fe)

------------------------------------------------------------------------------------------
-- Strict Glue types
------------------------------------------------------------------------------------------

opaque
  Glueᶠ : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ]))
    → Γ ⊢ᶠType ℓ
  Glueᶠ φ B A fe =
    ≅Realignᶠ φ (WeakGlueᶠ φ B A fe) A (domIsoGlueᴵ φ (fstᴵ fe))

opaque
  unfolding Glueᶠ
  GlueᶠMatch : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ]))
    → A ≡ Glueᶠ φ B A fe ∘ᶠ wk[ φ ]
  GlueᶠMatch φ B A fe =
    ≅RealignᶠMatch φ _ _ (domIsoGlueᴵ φ (fstᴵ fe))

opaque
  unfolding Glueᶠ
  reindexGlueᶠ : {φ : Γ → Cof}
    {B : Γ ⊢ᶠType ℓ}
    {A : Γ ▷[ φ ] ⊢ᶠType ℓ}
    {fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ A (B ∘ᶠ wk[ φ ])}
    (ρ : Δ → Γ)
    → Glueᶠ φ B A fe ∘ᶠ ρ ≡ Glueᶠ (φ ∘ ρ) (B ∘ᶠ ρ) (A ∘ᶠ ρ ×id) (fe ∘ ρ ×id)
  reindexGlueᶠ {φ = φ} ρ =
    reindexRealignᶠ _
    ∙
    cong
      (λ β' → ≅Realignᶠ _ (_ , β') _ (domIsoGlueᴵ (φ ∘ ρ) _))
      (reindexWeakGlueFibStr _)
