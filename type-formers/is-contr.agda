{-

Definition of contractibility within the fibrant type theory.
A contractible fibration is a trivial fibration and vice versa.

-}
module type-formers.is-contr where

open import prelude
open import axioms
open import cofibration
open import fibration.coercion
open import fibration.fibration
open import fibration.trivial
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Homotopy-contractibility
------------------------------------------------------------------------------------------

IsContr : Type ℓ → Type ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContrᴵ : (Γ → Type ℓ) → (Γ → Type ℓ)
IsContrᴵ A x = IsContr (A x)

opaque
  IsContrFibStr : {A : Γ → Type ℓ} (α : FibStr A) → FibStr (IsContrᴵ A)
  IsContrFibStr α  =
    ΣFibStr α (ΠFibStr (α ∘ᶠˢ fst) (PathFibStr (α ∘ᶠˢ fst ∘ᶠˢ fst) snd (snd ∘ fst)))

  reindexIsContrFibStr : {A : Γ → Type ℓ} {α : FibStr A} (ρ : Δ → Γ)
    → IsContrFibStr α ∘ᶠˢ ρ ≡ IsContrFibStr (α ∘ᶠˢ ρ)
  reindexIsContrFibStr ρ =
    reindexΣFibStr _
    ∙ cong (ΣFibStr _) (reindexΠFibStr _ ∙ cong (ΠFibStr _) (reindexPathFibStr _))

IsContrᶠ : Γ ⊢ᶠType ℓ → Γ ⊢ᶠType ℓ
IsContrᶠ A .fst = IsContrᴵ (A .fst)
IsContrᶠ A .snd = IsContrFibStr (A .snd)

isContrToTFibStr : (A : Γ ⊢ᶠType ℓ) (c : Γ ⊢ᶠ IsContrᶠ A) → TFibStr (A .fst)
isContrToTFibStr A c γ φ a =
  subst (A .fst γ [ φ ↦_]) (funExt λ u → c γ .snd (a u) .at0) $
  A .snd .lift 𝕚 1 (cst γ) box .fill 0
  where
  box : OpenBox 𝕚 1 (cst (A .fst γ))
  box .cof = φ
  box .tube i u = c γ .snd (a u) .at i
  box .cap .out = c γ .fst
  box .cap .out≡ u = c γ .snd (a u) .at1

TFibToIsContr : (A : Γ ⊢ᶠTriv ℓ) → Γ ⊢ᶠ IsContrᶠ (TFibToFib A)
TFibToIsContr A γ = (center , contract)
  where
  center = A .snd γ ⊥ (λ ()) .out

  ext : (a : A .fst γ) (i : 𝕀) → A .fst γ [ ∂ i ↦ _ ]
  ext a i = A .snd γ (∂ i) (∂-rec i (cst a) (cst center))

  contract : (a : A .fst γ) → a ~ center
  contract a .at i = ext a i .out
  contract a .at0 = sym (ext a 0 .out≡ (∨l refl))
  contract a .at1 = sym (ext a 1 .out≡ (∨r refl))
