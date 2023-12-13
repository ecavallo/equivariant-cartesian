{-

Postulates realignment of isomorphisms-up-to-strict-equality along cofibrations for the
universes of the ambient type theory.

-}
module axiom.realignment where

open import prelude
open import internal-extensional-type-theory
open import cofibration

private variable ℓ : Level

------------------------------------------------------------------------------------------
-- We postulate realignment of isomorphisms along cofibrations for the universes of the
-- ambient type theory.
------------------------------------------------------------------------------------------

postulate
  ≅Realigns : (φ : Cof) (B : Type ℓ)
    (A : [ φ ] → Σ (Type ℓ) (_≅ B)) → Σ (Type ℓ) (_≅ B) [ φ ↦ A ]

------------------------------------------------------------------------------------------
-- Convenience functions unpacking the components of the postulated realignment for
-- isomorphisms
------------------------------------------------------------------------------------------

≅Realign : (φ : Cof) {B : Type ℓ} {A : [ φ ] → Type ℓ} (e : (u : [ φ ]) → A u ≅ B)
  → Type ℓ
≅Realign φ e = ≅Realigns φ _ (_ ,, e) .out .fst

≅realign : (φ : Cof) {B : Type ℓ} {A : [ φ ] → Type ℓ} (e : (u : [ φ ]) → A u ≅ B)
  → ≅Realign φ e ≅ B
≅realign φ e = ≅Realigns φ _ (_ ,, e) .out .snd

≅RealignMatch : (φ : Cof) {B : Type ℓ} {A : [ φ ] → Type ℓ} (e : (u : [ φ ]) → A u ≅ B)
  → ∀ u → A u ≡ ≅Realign φ e
≅RealignMatch φ e u = cong fst (≅Realigns φ _ (_ ,, e) .out≡ u)

≅realignMatch : (φ : Cof) {B : Type ℓ} {A : [ φ ] → Type ℓ} (e : (u : [ φ ]) → A u ≅ B)
  → ∀ u → subst (_≅ B) (≅RealignMatch φ e u) (e u) ≡ ≅realign φ e
≅realignMatch φ e u = Σeq₂ (≅Realigns φ _ (_ ,, e) .out≡ u) _
