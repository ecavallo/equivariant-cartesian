{-

Postulates a type of shapes, types of homomorphisms between shapes,
and the interval shape

-}
{-# OPTIONS --rewriting #-}
module axioms.shape where

open import prelude
open import axioms.funext

----------------------------------------------------------------------
-- Shapes
----------------------------------------------------------------------

postulate
  Shape : Set
  ShapeHom : Shape → Shape → Set

  ⟨_⟩ : Shape → Set
  ⟪_⟫ : {I J : Shape} → ShapeHom I J → ⟨ I ⟩ → ⟨ J ⟩

  int : Shape

Int = ⟨ int ⟩

postulate
  O : Int
  I : Int
  O≠I   : ∀ {ℓ} {A : Set ℓ} → O ≡ I → A
