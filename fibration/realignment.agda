{-

Realign a fibration structure to agree with another on some cofibration

-}
module fibration.realignment where

open import prelude
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Realigning a fibration structure on a given family
------------------------------------------------------------------------------------------

module RealignLift {S r} (φ : ⟨ S ⟩ → Cof)
  {B : ⟨ S ⟩ → Type ℓ} (β : FibStr B)
  (α : FibStr (B ∘ wk[ φ ]))
  (box : OpenBox S r B)
  where

  fillA : [ all S φ ] → _
  fillA u = α .lift S r (id ,, u) box

  box' : OpenBox S r B
  box' .cof = box .cof ∨ all S φ
  box' .tube i =
    ∨-rec
      (box .tube i)
      (λ u → fillA u .fill i .out)
      (λ v u → fillA u .fill i .out≡ v)
  box' .cap .out = box .cap .out
  box' .cap .out≡ =
    ∨-elimEq
      (box .cap .out≡)
      (λ u → fillA u .cap≡)

  fillB = β .lift S r id box'

  filler : Filler box
  filler .fill s .out = fillB .fill s .out
  filler .fill s .out≡ v = fillB .fill s .out≡ (∨l v)
  filler .cap≡ = fillB .cap≡

module RealignVary {S T} (σ : ShapeHom S T) {r}
  (φ : ⟨ T ⟩ → Cof)
  {B : ⟨ T ⟩ → Type ℓ} (β : FibStr B)
  (α : FibStr (B ∘ wk[ φ ]))
  (box : OpenBox T (⟪ σ ⟫ r) B)
  where

  module T = RealignLift φ β α box
  module S =
    RealignLift (φ ∘ ⟪ σ ⟫)
      (β ∘ᶠˢ ⟪ σ ⟫) (α ∘ᶠˢ ⟪ σ ⟫ ×id) (reshapeBox σ box)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    β .vary S T σ r id T.box' s
    ∙
    cong
      (λ box' → β .lift S r ⟪ σ ⟫ box' .fill s .out)
      (boxExt
        (cong (box .cof ∨_) (allEquivariant σ φ))
        (λ i → takeOutCof (box .cof) (all T φ) (all S (φ ∘ ⟪ σ ⟫))
          (λ _ → refl)
          (λ uS uT →
            α .vary S T σ r (id ,, uS) box i
            ∙ cong (λ w → α .lift S r (⟪ σ ⟫ ,, w) (reshapeBox σ box) .fill i .out)
              (funExt λ s → cofIsProp' (φ (⟪ σ ⟫ s)))))
        refl)

opaque
  realignFibStr : (φ : Γ → Cof)
    {B : Γ → Type ℓ} (β : FibStr B)
    (α : FibStr (B ∘ wk[ φ ]))
    → FibStr B
  realignFibStr φ β α .lift S r p =
    RealignLift.filler (φ ∘ p) (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id)
  realignFibStr φ β α .vary S T σ r p =
    RealignVary.eq σ (φ ∘ p) (β ∘ᶠˢ p) (α ∘ᶠˢ p ×id)

  -- TODO prove this in RealignLift?
  isRealigned : (φ : Γ → Cof)
    {B : Γ → Type ℓ} (β : FibStr B)
    (α : FibStr (B ∘ wk[ φ ]))
    → α ≡ realignFibStr φ β α ∘ᶠˢ 𝒑
  isRealigned φ β α =
    FibStrExt λ S r p box s →
      RealignLift.fillB _ (β ∘ᶠˢ (wk[ φ ] ∘ p)) (α ∘ᶠˢ (wk[ φ ] ∘ p) ×id) _
      .fill s .out≡ (∨r (𝒒 ∘ p))

  reindexRealignFibStr : {φ : Γ → Cof}
    {B : Γ → Type ℓ} {β : FibStr B}
    {α : FibStr (B ∘ wk[ φ ])}
    (ρ : Δ → Γ)
    → realignFibStr φ β α ∘ᶠˢ ρ ≡ realignFibStr (φ ∘ ρ) (β ∘ᶠˢ ρ) (α ∘ᶠˢ ρ ×id)
  reindexRealignFibStr ρ = FibStrExt λ S r p box s → refl

------------------------------------------------------------------------------------------
-- Realigning a fibration
------------------------------------------------------------------------------------------

opaque
  ≅Realignᶠ : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ A .fst ≅ˣ (B .fst ∘ wk[ φ ]))
    → Γ ⊢ᶠType ℓ
  ≅Realignᶠ φ _ _ iso .fst γ = ≅Realign (φ γ) (iso ∘ (γ ,_))
  ≅Realignᶠ φ (_ , β) (_ , α) iso .snd =
    realignFibStr φ
      (isomorphFibStr (λ γ → ≅realign (φ γ) (iso ∘ (γ ,_))) β)
      (subst FibStr (funExt (uncurry λ γ → ≅RealignMatch (φ γ) (iso ∘ (γ ,_)))) α)

  ≅RealignᶠMatch : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ A .fst ≅ˣ (B .fst ∘ wk[ φ ]))
    → A ≡ ≅Realignᶠ φ B A iso ∘ᶠ wk[ φ ]
  ≅RealignᶠMatch _ _ _ _ =
    Σext _ (isRealigned _ _ _)

  ≅realignᶠ : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ A .fst ≅ˣ (B .fst ∘ wk[ φ ]))
    → Γ ⊢ˣ ≅Realignᶠ φ B A iso .fst ≅ˣ B .fst
  ≅realignᶠ φ B A iso γ = ≅realign _ _

  ≅realignᶠMatch : (φ : Γ → Cof)
    (B : Γ ⊢ᶠType ℓ)
    (A : Γ ▷[ φ ] ⊢ᶠType ℓ)
    (iso : Γ ▷[ φ ] ⊢ˣ A .fst ≅ˣ (B .fst ∘ wk[ φ ]))
    → subst
        (λ C → Γ ▷[ φ ] ⊢ˣ C .fst ≅ˣ (B .fst ∘ wk[ φ ]))
        (≅RealignᶠMatch φ B A iso)
        iso
      ≡ ≅realignᶠ φ B A iso ∘ wk[ φ ]
  ≅realignᶠMatch φ B A iso =
    funExt λ (γ , u) →
    substNaturality {B = λ C → _ ⊢ˣ C .fst ≅ˣ (B .fst ∘ wk[ φ ])} (λ _ → _$ (γ , u))
      (≅RealignᶠMatch φ B A iso)
    ∙ substCongAssoc (λ C → C ≅ B .fst γ) ((_$ (γ , u)) ∘ fst) (≅RealignᶠMatch φ B A iso) _
    ∙ cong (subst (_≅ B .fst γ) ⦅–⦆ (iso (γ , u))) uip'
    ∙ ≅realignMatch (φ γ) (iso ∘ (γ ,_)) u

  reindexRealignᶠ : {φ : Γ → Cof}
    {B : Γ ⊢ᶠType ℓ}
    {A : Γ ▷[ φ ] ⊢ᶠType ℓ}
    {iso : Γ ▷[ φ ] ⊢ˣ A .fst ≅ˣ (B .fst ∘ wk[ φ ])}
    (ρ : Δ → Γ)
    → ≅Realignᶠ φ B A iso ∘ᶠ ρ ≡ ≅Realignᶠ (φ ∘ ρ) (B ∘ᶠ ρ) (A ∘ᶠ ρ ×id) (iso ∘ ρ ×id)
  reindexRealignᶠ {A = _ , α} ρ =
    Σext refl
      (reindexRealignFibStr _
        ∙ cong₂ (realignFibStr _)
            (reindexIsomorphFibStr (λ _ → ≅realign _ _) _)
            (reindexSubst α _ _ _))
