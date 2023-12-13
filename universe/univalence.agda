{-

The universe is univalent, proven using Glue types. We follow Cohen, Coquand, Huber, and
Mörtberg (https://doi.org/10.4230/LIPIcs.TYPES.2015.5, §7.2), who prove univalence in the
form

(A : 𝑼) → IsContr (Σ B : 𝑼. El B ≃ El A).

The addition of an equivariance condition on fibrations has no effect on this proof.

-}
open import prelude
open import axiom
open import cofibration
open import fibration.fibration
open import fibration.trivial
open import type-former.equiv
open import type-former.hlevels
open import type-former.path
open import type-former.pi
open import type-former.sigma
open import universe.core
open import universe.fibrant
open import universe.glue

module universe.univalence where

UATFib : ∀ (@♭ ℓ) → TFibStr (Σˣ (𝑼ˣ ℓ) (Equivˣ (Elˣ snd) (Elˣ fst)))
UATFib ℓ B φ Part = filler
  where
  ExtendedTy : 𝑼 ℓ
  ExtendedTy = Glueᵁ φ B (fst ∘ Part) (snd ∘ Part)

  extendedEquiv : Equiv (El ExtendedTy) (El B)
  extendedEquiv = unglueᵁEquiv

  partEquiv : [ φ ] → Equiv (El ExtendedTy) (El B)
  partEquiv u =
    subst (Equiv ⦅–⦆ (El B) ∘ El) (GlueᵁMatch _ _ _ _ _) (Part u .snd)

  partFun≡extendedFun : ∀ u → partEquiv u .fst ≡ extendedEquiv .fst
  partFun≡extendedFun u =
    substNaturality (λ _ → fst) (GlueᵁMatch _ _ _ _ _) ∙
    unglueᵁMatch u

  fixPath : (u : [ φ ]) → partEquiv u ~ extendedEquiv
  fixPath u =
    equivPathᶠ (Elᶠ (cst ExtendedTy)) (Elᶠ (cst B)) _ _
      (cst $ eqToPath $ partFun≡extendedFun u)
      tt

  box : OpenBox 𝕚 1 (cst (Σ A ∈ 𝑼 ℓ , Equiv (El A) (El B)))
  box .cof = φ
  box .tube i u .fst = ExtendedTy
  box .tube i u .snd = fixPath u .at i
  box .cap .out .fst = ExtendedTy
  box .cap .out .snd = extendedEquiv
  box .cap .out≡ u = Σext refl (fixPath u .at1)

  filler : Σˣ (𝑼ˣ ℓ) (Equivˣ (Elˣ (λ r → snd r)) (Elˣ (λ r → fst r))) B [ φ ↦ Part ]
  filler .out =
    Σᶠ (𝑼ᶠ ℓ) (Equivᶠ (Elᶠ snd) (Elᶠ fst)) .snd .lift 𝕚 1 (λ _ → B) box .fill 0 .out
  filler .out≡ u =
    Σext (GlueᵁMatch _ _ _ _ _) (sym (fixPath u .at0))
    ∙ Σᶠ (𝑼ᶠ ℓ) (Equivᶠ (Elᶠ snd) (Elᶠ fst)) .snd .lift 𝕚 1 (λ _ → B) box .fill 0 .out≡ u

UA : ∀ (@♭ ℓ) → 𝟙 ⊢ᶠ Πᶠ (𝑼ᶠ ℓ) (IsContrᶠ (Σᶠ (𝑼ᶠ ℓ) (Equivᶠ (Elᶠ snd) (Elᶠ (snd ∘ fst)))))
UA ℓ = λˣ $ TFibToIsContr (_ , UATFib ℓ) ∘ snd
