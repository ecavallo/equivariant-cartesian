{-

Univalence from Glue types

-}
open import prelude
open import axioms
open import fibration.coercion
open import fibration.fibration
open import type-formers.equivs
open import type-formers.glue
open import type-formers.paths
open import type-formers.pi
open import type-formers.union

private variable
  ℓ : Level
  Γ : Type ℓ

fibExtInconsistent : {A B : Γ ⊢ᶠType ℓ} → ¬ Γ → A ≡ B
fibExtInconsistent ¬Γ =
  Σext
    (funExt $ 𝟘-rec ∘ ¬Γ)
    (FibStrExt λ _ r p _ _ → 𝟘-rec (¬Γ (p r)))

module _ (A B : Γ ⊢ᶠType ℓ) (e : Γ ⊢ᶠ Equivᶠ A B) where

  module UADom =
    Unionᶠ ((𝕚 ∋_≈ 0) ∘ snd) ((𝕚 ∋_≈ 1) ∘ snd)
      (A ∘ᶠ fst ∘ᶠ fst)
      (B ∘ᶠ fst ∘ᶠ fst)
      (fibExtInconsistent λ (_ , _ , i≡0 , i≡1) → 0≠1 (sym i≡0 ∙ i≡1))

  uaDom : Γ ▷⟨ 𝕚 ⟩ ▷[ ∂ ∘ snd ] ⊢ᶠType ℓ
  uaDom = UADom.fib

  opaque
    uaEquiv : Γ ▷𝕀 ▷[ ∂ ∘ snd ] ⊢ᶠ Equivᶠ uaDom (B ∘ᶠ fst ∘ᶠ fst)
    uaEquiv =
      uncurry λ (γ , i) →
      ∂-elim i (λ _ → e γ) (λ _ → idEquivᶠ B γ)

  ua : Γ ▷𝕀 ⊢ᶠType ℓ
  ua = Glueᶠ (∂ ∘ snd) (B ∘ᶠ fst) uaDom uaEquiv

  ua∂ : ua ∘ᶠ wk[ ∂ ∘ snd ] ≡ uaDom
  ua∂ = sym (GlueᶠMatch _ _ _ _)

  ua₀ : ua ∘ᶠ (id ,, λ _ → 0) ≡ A
  ua₀ =
    cong (_∘ᶠ ρ) (cong (_∘ᶠ id× ∨l) ua∂ ∙ UADom.left)
    where
    ρ = id ,, (λ _ → 0) ,, λ _ → refl

  ua₁ : ua ∘ᶠ (id ,, λ _ → 1) ≡ B
  ua₁ =
    cong (_∘ᶠ ρ) (cong (_∘ᶠ id× ∨r) ua∂ ∙ UADom.right)
    where
    ρ = id ,, (λ _ → 1) ,, λ _ → refl

  -- TODO
  -- uaβ : Γ ⊢ᶠ Pathᶠ (A →ᶠ B) {!!} (equivFun e)
  -- uaβ = {!!}
