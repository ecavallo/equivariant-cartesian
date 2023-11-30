{-

Fibration extension property for the category of generating trivial cofibrations

TODO add comments

-}
{-# OPTIONS --rewriting #-}
module fibration.extension where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.sigma
open import type-formers.union
open import type-formers.equivs
open import type-formers.glue

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

record LargeOpenBox (S : Shape) {Γ : Type ℓ} (r : Γ → ⟨ S ⟩) ℓ' : Type (ℓ ⊔ lsuc ℓ')
  where
  constructor makeLargeBox
  field
    cof : Γ → Cof
    Tube : Γ ▷⟨ S ⟩ ▷[ cof ∘ fst ] ⊢ᶠType ℓ'
    Cap : Γ ⊢ᶠType ℓ'
    match : Tube ∘ᶠ (id ,, r) ×id ≡ Cap ∘ᶠ wk[ cof ]

open LargeOpenBox public

reshapeLargeBox : {S T : Shape} (σ : ShapeHom S T) {r : Γ → ⟨ S ⟩}
  → LargeOpenBox T (⟪ σ ⟫ ∘ r) ℓ → LargeOpenBox S r ℓ
reshapeLargeBox σ box .cof = box .cof
reshapeLargeBox σ box .Tube = box .Tube ∘ᶠ id× ⟪ σ ⟫ ×id
reshapeLargeBox σ box .Cap = box .Cap
reshapeLargeBox σ box .match = box .match

reindexLargeBox : {S : Shape} {r : Γ → ⟨ S ⟩}
  → LargeOpenBox S r ℓ → (ρ : Δ → Γ) → LargeOpenBox S (r ∘ ρ) ℓ
reindexLargeBox box ρ .cof = box .cof ∘ ρ
reindexLargeBox box ρ .Tube = box .Tube ∘ᶠ ρ ×id ×id
reindexLargeBox box ρ .Cap = box .Cap ∘ᶠ ρ
reindexLargeBox box ρ .match = cong (_∘ᶠ (ρ ×id)) (box .match)

largeBoxExt : {S : Shape} {r : Γ → ⟨ S ⟩}
  {box box' : LargeOpenBox S r ℓ}
  (cof≡ : box .cof ≡ box' .cof)
  → subst (λ φ → Γ ▷⟨ S ⟩ ▷[ φ ∘ fst ] ⊢ᶠType ℓ) cof≡ (box .Tube) ≡ box' .Tube
  → box .Cap ≡ box' .Cap
  → box ≡ box'
largeBoxExt refl refl refl = cong (makeLargeBox _ _ _) uip'

record LargeFiller {S : Shape} {Γ : Type ℓ} {r : Γ → ⟨ S ⟩}
  (box : LargeOpenBox S r ℓ') : Type (ℓ ⊔ lsuc ℓ')
  where
  field
    Fill : Γ ▷⟨ S ⟩ ⊢ᶠType ℓ'
    Tube≡ : Fill ∘ᶠ wk[ box .cof ∘ fst ] ≡ box .Tube
    Cap≡ : Fill ∘ᶠ (id ,, r) ≡ box .Cap

open LargeFiller public

-- TODO move
_⇒_ : Cof → Cof → Type
φ ⇒ ψ = [ φ ] → [ ψ ]

_⇒ᴵ_ : (Γ → Cof) → (Γ → Cof) → (Γ → Type)
(φ ⇒ᴵ ψ) γ = φ γ ⇒ ψ γ


module LargeBoxUnion {S} {r : Γ → ⟨ S ⟩}
  (box : LargeOpenBox S r ℓ)
  (s : Γ → ⟨ S ⟩)
  (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
  where

  open LargeOpenBox box renaming (cof to φ ; Tube to Tu ; Cap to Ca ; match to p)

  opaque
    eqLemma :
      _≡_
        {A = Γ ▷[ φ ] ▷[ ψ ∘ wk[ φ ] ] → Γ ▷⟨ S ⟩ ▷[ φ ∘ fst ]}
        ((id ,, r) ×id ∘ wk[ ψ ∘ wk[ φ ] ])
        ((id ,, s) ×id ∘ wk[ ψ ∘ wk[ φ ] ])
    eqLemma =
      funExt λ ((γ , u) , v) →
      Σext (cong (γ ,_) (toEq _ v)) (cofIsProp' (φ γ))

    matchLemma :
      Tu ∘ᶠ (id ,, s) ×id ∘ᶠ wk[ ψ ∘ wk[ φ ] ] ≡ Ca ∘ᶠ wk[ φ ] ∘ᶠ wk[ ψ ∘ wk[ φ ] ]
    matchLemma =
      cong (Tu ∘ᶠ_) (sym eqLemma) ∙ cong (_∘ᶠ wk[ ψ ∘ wk[ φ ] ]) p

  open Unionᶠ φ ψ
    (Tu ∘ᶠ (id ,, s) ×id)
    (Ca ∘ᶠ wk[ ψ ])
    matchLemma
    public

LargeBoxUnion : ∀ {S} {r : Γ → ⟨ S ⟩}
  (box : LargeOpenBox S r ℓ)
  (s : Γ → ⟨ S ⟩)
  (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
  → Γ ▷[ box .cof ∨ᴵ ψ ] ⊢ᶠType ℓ
LargeBoxUnion = LargeBoxUnion.fib

opaque
  varyLargeBoxUnion : ∀ {S T} (σ : ShapeHom S T) {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox T (⟪ σ ⟫ ∘ r) ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    → LargeBoxUnion box (⟪ σ ⟫ ∘ s) ψ ((cong ⟪ σ ⟫ ∘_) ∘ toEq) .snd
      ≡ LargeBoxUnion (reshapeLargeBox σ box) s ψ toEq .snd
  varyLargeBoxUnion σ box s ψ toEq =
    unionFibStrExt (box .cof) ψ (T.F.left ∙ sym S.F.left) (T.F.right ∙ sym S.F.right)
    where
    module S = LargeBoxUnion (reshapeLargeBox σ box) s ψ toEq
    module T = LargeBoxUnion box (⟪ σ ⟫ ∘ s) ψ ((cong ⟪ σ ⟫ ∘_) ∘ toEq)

opaque
  reindexLargeBoxUnion : ∀ {S} {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox S r ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    (ρ : Δ → Γ)
    → (LargeBoxUnion box s ψ toEq ∘ᶠ ρ ×id) .snd
      ≡ LargeBoxUnion (reindexLargeBox box ρ) (s ∘ ρ) (ψ ∘ ρ) (toEq ∘ ρ) .snd
  reindexLargeBoxUnion box s ψ toEq ρ =
    unionFibStrExt (box .cof ∘ ρ) (ψ ∘ ρ)
      (cong (_∘ᶠˢ ρ ×id) Γ.F.left ∙ sym Δ.F.left)
      (cong (_∘ᶠˢ ρ ×id) Γ.F.right ∙ sym Δ.F.right)
    where
    module Γ = LargeBoxUnion box s ψ toEq
    module Δ = LargeBoxUnion (reindexLargeBox box ρ) (s ∘ ρ) (ψ ∘ ρ) (toEq ∘ ρ)

opaque
  largeBoxEquiv : ∀ {S} {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox S r ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    → Γ ▷[ box .cof ∨ᴵ ψ ] ⊢ᶠ
      Equivᶠ (LargeBoxUnion box s ψ toEq) (box .Cap ∘ᶠ wk[ box .cof ∨ᴵ ψ ])
  largeBoxEquiv {S = S} {r} box s ψ toEq =
    uncurry λ γ →
    ∨-elim (φ γ) (ψ γ) (curry leftEquiv γ) (curry rightEquiv γ) (matchEquiv γ)
    where
    open LargeOpenBox box renaming (cof to φ ; Tube to Tu ; Cap to Ca ; match to mat)
    module Un = LargeBoxUnion box s ψ toEq

    leftEquiv : _ ▷[ φ ] ⊢ᶠ Equivᶠ (Tu ∘ᶠ (id ,, s) ×id) (Ca ∘ᶠ wk[ φ ])
    leftEquiv (γ , u) =
      subst
        (Equiv (Tu .fst _))
        (appCong (cong fst mat))
        (coerceEquiv S (Tu ∘ᶠ ((γ ,_) ,, λ _ → u)) (s γ) (r γ))

    rightEquiv : _ ▷[ ψ ] ⊢ᶠ Equivᶠ (Ca ∘ᶠ wk[ ψ ]) (Ca ∘ᶠ wk[ ψ ])
    rightEquiv (γ , _) = idEquivᶠ (Ca ∘ᶠ (λ _ → γ))

    eqLemma : {Γ : Type ℓ} {γ : Γ} {A : Type ℓ'} {B D : Γ ⊢ᶠType ℓ'}
      (eqAD : A ≡ D .fst γ) (eqAB : A ≡ B .fst γ)
      (eqBD : B ≡ D)
      {e : Equiv A (B .fst _)}
      → subst (Equiv ⦅–⦆ _) eqAB e ≡ idEquiv (B .snd ∘ᶠˢ (λ _ → γ))
      → subst (Equiv ⦅–⦆ _) eqAD (subst (Equiv A) (appCong (cong fst eqBD)) e)
        ≡ idEquiv (D .snd ∘ᶠˢ (λ _ → γ))
    eqLemma refl refl refl eq = eq

    matchEquiv : ∀ γ (u : [ φ γ ]) (v : [ ψ γ ])
      → subst
          (λ w → Equiv (Un.fib .fst (γ , w)) (Ca .fst γ))
          (trunc (∨l u) (∨r v))
          (leftEquiv (γ , u))
        ≡ rightEquiv (γ , v)
    matchEquiv γ u v =
      substCongAssoc (Equiv ⦅–⦆ _) (Un.fib .fst ∘ (γ ,_)) (trunc (∨l u) (∨r v)) _
      ∙
      eqLemma
        (cong (Un.fib .fst ∘ (γ ,_)) (trunc (∨l u) (∨r v)))
        (cong (Tu .fst ∘ ((γ ,_) ,, λ _ → u)) (sym (toEq γ v)))
        mat
        (sym
          (substCongAssoc
            (Equiv ⦅–⦆ _)
            (Tu .fst ∘ ((γ ,_) ,, λ _ → u))
            (sym (toEq γ v))
            _)
          ∙ congdep (coerceEquiv S (Tu ∘ᶠ ((γ ,_) ,, λ _ → u)) ⦅–⦆ (r γ)) (sym (toEq γ v))
          ∙ coerceEquivCap S (Tu ∘ᶠ ((γ ,_) ,, λ _ → u)) (r γ))

opaque
  unfolding largeBoxEquiv
  varyLargeBoxEquiv : ∀ {S T} (σ : ShapeHom S T) {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox T (⟪ σ ⟫ ∘ r) ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    → largeBoxEquiv box (⟪ σ ⟫ ∘ s) ψ ((cong ⟪ σ ⟫ ∘_) ∘ toEq)
      ≡ largeBoxEquiv (reshapeLargeBox σ box) s ψ toEq
  varyLargeBoxEquiv σ {r = r} box s ψ toEq =
    funExt $
    uncurry λ γ →
    ∨-elimEq (φ γ) (ψ γ)
      (λ u →
        cong (subst (Equiv (Tu .fst _)) (appCong (cong fst mat)))
          (coerceEquivVary σ (Tu ∘ᶠ ((γ ,_) ,, λ _ → u)) (s γ) (r γ)))
      (λ v → refl)
    where
    open LargeOpenBox box renaming (cof to φ ; Tube to Tu ; match to mat)

opaque
  unfolding largeBoxEquiv
  reindexLargeBoxEquiv : ∀ {S} {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox S r ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    (ρ : Δ → Γ)
    → largeBoxEquiv box s ψ toEq ∘ (ρ ×id)
      ≡ largeBoxEquiv (reindexLargeBox box ρ) (s ∘ ρ) (ψ ∘ ρ) (toEq ∘ ρ)
  reindexLargeBoxEquiv {S = S} {r = r} box s ψ toEq ρ =
    funExt $
    uncurry λ δ →
    ∨-elimEq (φ (ρ δ)) (ψ (ρ δ))
      (λ u →
        cong
          (subst (Equiv (Tu .fst _)) ⦅–⦆
            (coerceEquiv S (Tu ∘ᶠ ((ρ δ ,_) ,, λ _ → u)) (s (ρ δ)) (r (ρ δ))))
          uip')
      (λ v → refl)
    where
    open LargeOpenBox box renaming (cof to φ ; Tube to Tu)

opaque
  LargeBoxFillerψ : ∀ {S} {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox S r ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    → Γ ⊢ᶠType ℓ
  LargeBoxFillerψ box s ψ toEq =
    SGlueᶠ
      (box .cof ∨ᴵ ψ)
      (box .Cap)
      (LargeBoxUnion box s ψ toEq)
      (largeBoxEquiv box s ψ toEq)

  reindexLargeBoxFillerψ : ∀ {S} {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox S r ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    (ρ : Δ → Γ)
    → LargeBoxFillerψ box s ψ toEq ∘ᶠ ρ
      ≡ LargeBoxFillerψ (reindexLargeBox box ρ) (s ∘ ρ) (ψ ∘ ρ) (toEq ∘ ρ)
  reindexLargeBoxFillerψ box s ψ toEq ρ =
    reindexSGlueᶠ _
    ∙ cong₂
      (curry (SGlueᶠ ((box .cof ∨ᴵ ψ) ∘ ρ) (box .Cap ∘ᶠ ρ)) _)
      (reindexLargeBoxUnion box s ψ toEq ρ)
      (reindexLargeBoxEquiv _ _ _ _ _)

opaque
  unfolding LargeBoxFillerψ
  LargeBoxψTube≡ : ∀ {S} {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox S r ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    → LargeBoxFillerψ box s ψ toEq ∘ᶠ wk[ box .cof ] ≡ box .Tube ∘ᶠ ((id ,, s) ×id)
  LargeBoxψTube≡ box s ψ toEq =
    cong (_∘ᶠ id× ∨l) (sym (SGlueᶠStrictness _ _ _ _))
    ∙ LargeBoxUnion.left _ _ _ _

opaque
  unfolding LargeBoxFillerψ
  LargeBoxCap≡ : ∀ {S} {r : Γ → ⟨ S ⟩} (box : LargeOpenBox S r ℓ)
    → LargeBoxFillerψ box r (S ∋ r ≈ᴵ r) (λ _ → id) ≡ box .Cap
  LargeBoxCap≡ box =
    cong (_∘ᶠ (id ,, λ _ → ∨r refl)) (sym (SGlueᶠStrictness _ _ _ _))
    ∙ cong (_∘ᶠ (id ,, λ _ → refl)) (LargeBoxUnion.right box _ _ _)

LargeBoxFiller : ∀ {S} {r : Γ → ⟨ S ⟩}
  (box : LargeOpenBox S r ℓ) → LargeFiller box
LargeBoxFiller {S = S} {r = r} box .Fill =
  LargeBoxFillerψ (reindexLargeBox box fst) snd (S ∋ (r ∘ fst) ≈ᴵ snd) (λ _ → id)
LargeBoxFiller {S = S} {r} box .Tube≡ =
  LargeBoxψTube≡ (reindexLargeBox box fst) snd (S ∋ (r ∘ fst) ≈ᴵ snd) (λ _ → id)
LargeBoxFiller {S = S} {r} box .Cap≡ =
  reindexLargeBoxFillerψ (reindexLargeBox box fst) snd (S ∋ (r ∘ fst) ≈ᴵ snd) (λ _ → id) (id ,, r)
  ∙ cong (λ box' → LargeBoxFillerψ box' r (S ∋ r ≈ᴵ r) (λ _ → id)) (largeBoxExt refl refl refl)
  ∙ LargeBoxCap≡ box

opaque
  unfolding LargeBoxFillerψ
  varyLargeBoxFillerψ : ∀ {S T} (σ : ShapeHom S T) {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox T (⟪ σ ⟫ ∘ r) ℓ)
    (s : Γ → ⟨ S ⟩)
    (ψ : Γ → Cof) (toEq : Γ ⊢ ψ ⇒ᴵ (S ∋ r ≈ᴵ s))
    → LargeBoxFillerψ box (⟪ σ ⟫ ∘ s) ψ ((cong ⟪ σ ⟫ ∘_) ∘ toEq)
      ≡ LargeBoxFillerψ (reshapeLargeBox σ box) s ψ toEq
  varyLargeBoxFillerψ σ box s ψ toEq =
    cong₂
      (curry (SGlueᶠ (box .cof ∨ᴵ ψ) (box .Cap)) _)
      (varyLargeBoxUnion σ box s ψ toEq)
      (varyLargeBoxEquiv _ _ _ _ _)

varyLargeBoxFiller : ∀ {S T} (σ : ShapeHom S T) {r : Γ → ⟨ S ⟩}
  (box : LargeOpenBox T (⟪ σ ⟫ ∘ r) ℓ)
  → LargeBoxFiller box .Fill ∘ᶠ (id× ⟪ σ ⟫) ≡ LargeBoxFiller (reshapeLargeBox σ box) .Fill
varyLargeBoxFiller {S = S} {T = T} σ {r = r} box =
  reindexLargeBoxFillerψ _ _ _ _ (id× ⟪ σ ⟫)
  ∙
  cong (LargeBoxFillerψ _ _ _) (funExt' $ funExt' uip')
  ∙
  varyLargeBoxFillerψ _ _ _ _ (λ γ → subst [_] (≈Equivariant σ _ _))
  ∙
  cong
    (λ box' → LargeBoxFillerψ box' snd (T ∋ _ ≈ᴵ _) (λ γ → subst [_] (≈Equivariant σ _ _)))
    (largeBoxExt refl refl refl)
  ∙
  congΣ (LargeBoxFillerψ _ _)
    (funExt' $ ≈Equivariant σ _ _)
    (funExt' $ funExt' uip')

reindexLargeBoxFiller :  ∀ {S} {r : Γ → ⟨ S ⟩}
    (box : LargeOpenBox S r ℓ) (ρ : Δ → Γ)
    → LargeBoxFiller box .Fill ∘ᶠ ρ ×id ≡ LargeBoxFiller (reindexLargeBox box ρ) .Fill
reindexLargeBoxFiller {S = S} {r = r} box ρ =
  reindexLargeBoxFillerψ _ _ _ _ (ρ ×id)
  ∙
  cong
    (λ box' → LargeBoxFillerψ box' snd (S ∋ (r ∘ ρ ∘ fst) ≈ᴵ snd) (λ _ → id))
    (largeBoxExt refl refl refl)
