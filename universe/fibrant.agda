{-

Fibrancy of the universe

TODO discuss non-use of fibration.extension

-}
module universe.fibrant where

open import prelude
open import axioms
open import cofibration
open import fibration.fibration
open import type-formers.equivs
open import type-formers.glue
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma
open import universe.core
open import universe.glue

private variable
  ℓ : Level
  Γ : Type ℓ

----------------------------------------------------------------------------------------
-- Fibrancy of the universe
----------------------------------------------------------------------------------------

module _ {@♭ ℓ} where

  module 𝑼Lift {S r} (box : OpenBox S r (𝑼ᴵ ℓ)) where

    partialEquiv : ∀ s
      → [ box .cof ∨ S ∋ r ≈ s ]
      → Σ A ∈ 𝑼 ℓ , Equiv (El A) (El (box .cap .out))
    partialEquiv s =
      ∨-rec (box .cof) (S ∋ r ≈ s)
        (λ u →
          box .tube s u ,
          subst (Equiv _ ∘ El) (box .cap .out≡ u) (coerceEquiv S (Elᶠ (box .tube ⦅–⦆ u)) s r))
        (λ _ → box .cap .out , idEquivᶠ (Elᶠ id) (box .cap .out))
        (λ {u refl →
          Σext
            (box .cap .out≡ u)
            (eqLemma (box .cap .out≡ u) (coerceEquivCap S (Elᶠ (box .tube ⦅–⦆ u)) r))})
      where
      eqLemma : {A B : 𝑼 ℓ} (eq : A ≡ B) {e : Equiv (El A) (El A)}
        → e ≡ idEquivᶠ (Elᶠ id) A
        → subst ((Equiv ⦅–⦆ _) ∘ El) eq (subst (Equiv _ ∘ El) eq e) ≡ idEquivᶠ (Elᶠ id) B
      eqLemma refl eq = eq

    filler : Filler box
    filler .fill s .out =
      Glueᵁ
        (box .cof ∨ S ∋ r ≈ s)
        (box .cap .out)
        (fst ∘ partialEquiv s)
        (snd ∘ partialEquiv s)
    filler .fill s .out≡ u = GlueᵁMatch _ _ _ _ (∨l u)
    filler .cap≡ = sym (GlueᵁMatch _ _ _ _ (∨r refl))

  opaque
    𝑼FibStr : FibStr {Γ = 𝟙} (𝑼ᴵ ℓ)
    𝑼FibStr .lift S r p box = 𝑼Lift.filler box
    𝑼FibStr .vary S T σ r p box s =
      congΣ
        (λ φ part → Glueᵁ φ (box .cap .out) (fst ∘ part) (snd ∘ part))
        cofEq
        (substDom [_] cofEq _
          ∙ funExt (λ uv → partialEquivEq (subst [_] (sym cofEq) uv) uv))
      where
      cofEq : (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (box .cof ∨ S ∋ r ≈ s)
      cofEq = cong (box .cof ∨_) (≈Equivariant σ r s)

      partialEquivEq : ∀ uv uv'
        → 𝑼Lift.partialEquiv box (⟪ σ ⟫ s) uv ≡ 𝑼Lift.partialEquiv (reshapeBox σ box) s uv'
      partialEquivEq uv =
        ∨-elimEq (box .cof) (S ∋ r ≈ s)
          (λ u →
            cong (𝑼Lift.partialEquiv box (⟪ σ ⟫ s)) (trunc uv (∨l u))
            ∙ Σext refl
              (cong (subst (Equiv _ ∘ El) (box .cap .out≡ u))
                (coerceEquivVary σ (Elᶠ (box .tube ⦅–⦆ u)) s r)))
          (λ {refl → cong (𝑼Lift.partialEquiv box (⟪ σ ⟫ s)) (trunc uv (∨r refl))})

𝑼ᶠ : ∀ (@♭ ℓ) → Γ ⊢ᶠType (lsuc ℓ )
𝑼ᶠ ℓ .fst = 𝑼ᴵ ℓ
𝑼ᶠ ℓ .snd = 𝑼FibStr ∘ᶠˢ cst tt
