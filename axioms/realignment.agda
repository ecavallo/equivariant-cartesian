{-

Postulates realignment of isomorphisms-up-to-strict-equality along cofibrations for the
universes of the ambient type theory.

-}
{-# OPTIONS --rewriting #-}
module axioms.realignment where

open import prelude
open import axioms.cofibration

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
≅Realign : (φ : Cof) (B : Type ℓ) (A : [ φ ] → Type ℓ) (e : (u : [ φ ]) → A u ≅ B)
  → Type ℓ
≅Realign φ B A e = ≅Realigns φ B (A ,, e) .out .fst

≅realign : (φ : Cof) (B : Type ℓ) (A : [ φ ] → Type ℓ) (e : (u : [ φ ]) → A u ≅ B)
  → ≅Realign φ B A e ≅ B
≅realign φ B A e = ≅Realigns φ B (A ,, e) .out .snd

≅RealignMatch : (φ : Cof) (B : Type ℓ) (A : [ φ ] → Type ℓ) (e : (u : [ φ ]) → A u ≅ B)
  → ∀ u → A u ≡ ≅Realign φ B A e
≅RealignMatch φ B A e u = cong fst (≅Realigns φ B (A ,, e) .out≡ u)

≅realignMatch : (φ : Cof) (B : Type ℓ) (A : [ φ ] → Type ℓ) (e : (u : [ φ ]) → A u ≅ B)
  → ∀ u → subst (_≅ B) (≅RealignMatch φ B A e u) (e u) ≡ ≅realign φ B A e
≅realignMatch φ B A e u = Σeq₂ (≅Realigns φ B (A ,, e) .out≡ u) _
