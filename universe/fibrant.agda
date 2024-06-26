{-

Fibrancy of the universe, derived from closure of the universe under Glue types.

-}
module universe.fibrant where

open import basic
open import axiom
open import cofibration
open import fibration.fibration
open import type-former.equiv
open import type-former.glue
open import type-former.path
open import type-former.pi
open import type-former.sigma
open import universe.core
open import universe.glue

private variable
  ℓ : Level
  Γ : Type ℓ

----------------------------------------------------------------------------------------
-- Fibrancy of the universe.
----------------------------------------------------------------------------------------

module _ {@♭ ℓ} where

  module 𝑼Lift {S r} (box : OpenBox S (𝑼ˣ ℓ) r) where

    tubeEquiv : ∀ s → [ box .cof ] → Σ A ∈ 𝑼 ℓ , El A ≃ El (box .cap .out)
    tubeEquiv s u .fst = box .tube s u
    tubeEquiv s u .snd =
      subst ((_ ≃_) ∘ El) (box .cap .out≡ u) (transpEquiv S (Elᶠ (box .tube ⦅–⦆ u)) s r)

    capEquiv : ∀ s → [ S ∋ r ≈ s ] → Σ A ∈ 𝑼 ℓ , El A ≃ El (box .cap .out)
    capEquiv s _ .fst = box .cap .out
    capEquiv s _ .snd = idEquivᶠ (Elᶠ id) (box .cap .out)

    opaque
      coh : ∀ s u v → tubeEquiv s u ≡ capEquiv s v
      coh s u refl =
        Σext
          (box .cap .out≡ u)
          (eqLemma (box .cap .out≡ u)
            (transpEquivCap S (Elᶠ (box .tube ⦅–⦆ u)) r
              ∙ cong$ (sym (reindexIdEquivᶠ (box .tube ⦅–⦆ u)))))
        where
        eqLemma : {A B : 𝑼 ℓ} (eq : A ≡ B) {e : El A ≃ El A}
          → e ≡ idEquivᶠ (Elᶠ id) A
          → subst ((_≃ _) ∘ El) eq (subst ((_ ≃_) ∘ El) eq e) ≡ idEquivᶠ (Elᶠ id) B
        eqLemma refl eq = eq

    partialEquiv : ∀ s
      → [ box .cof ∨ S ∋ r ≈ s ]
      → Σ A ∈ 𝑼 ℓ , El A ≃ El (box .cap .out)
    partialEquiv s = ∨-rec (tubeEquiv s) (capEquiv s) (coh s)

    opaque
      filler : Filler box
      filler .fill s .out =
        Glueᵁ
          (box .cof ∨ S ∋ r ≈ s)
          (box .cap .out)
          (fst ∘ partialEquiv s)
          (snd ∘ partialEquiv s)
      filler .fill s .out≡ u = GlueᵁMatch _ _ _ _ (∨l u)
      filler .cap≡ = sym (GlueᵁMatch _ _ _ _ (∨r refl))

  module 𝑼Vary {S T} (σ : Shape[ S , T ]) {r} (box : OpenBox T (𝑼ˣ ℓ) (⟪ σ ⟫ r))
    where

    module T = 𝑼Lift box
    module S = 𝑼Lift (reshapeBox σ box)

    opaque
      partialEquivEq : ∀ s uv uv'
        → T.partialEquiv (⟪ σ ⟫ s) uv ≡ S.partialEquiv s uv'
      partialEquivEq s uv =
        ∨-elimEq
          (λ u →
            cong
              (T.partialEquiv (⟪ σ ⟫ s))
              (cofIsStrictProp (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) uv (∨l u))
            ∙ Σext refl
              (cong
                (subst ((_ ≃_) ∘ El) (box .cap .out≡ u))
                (transpEquivVary σ (Elᶠ (box .tube ⦅–⦆ u)) s r)))
          (λ {refl →
            cong
              (T.partialEquiv (⟪ σ ⟫ s))
              (cofIsStrictProp (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) uv (∨r refl))})

    opaque
      unfolding 𝑼Lift.filler
      eq : ∀ s → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
      eq s =
        congΣ make
          cofEq
          (substDom [_] cofEq _
            ∙ funExt (λ uv → partialEquivEq s (subst [_] (sym cofEq) uv) uv))
        where
        make : (φ : Cof) (part : [ φ ] → Σ A ∈ 𝑼 ℓ , El A ≃ El (box .cap .out)) → 𝑼 ℓ
        make φ part = Glueᵁ φ (box .cap .out) (fst ∘ part) (snd ∘ part)

        cofEq : (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (box .cof ∨ S ∋ r ≈ s)
        cofEq = cong (box .cof ∨_) (≈Equivariant σ r s)


  opaque
    𝑼FibStr : FibStr {Γ = 𝟙} (𝑼ˣ ℓ)
    𝑼FibStr .lift S r γ box = 𝑼Lift.filler box
    𝑼FibStr .vary S T σ r γ box s = 𝑼Vary.eq σ box s

𝑼ᶠ : ∀ (@♭ ℓ) → Γ ⊢ᶠType (lsuc ℓ)
𝑼ᶠ ℓ .fst = 𝑼ˣ ℓ
𝑼ᶠ ℓ .snd = 𝑼FibStr ∘ᶠˢ cst tt
