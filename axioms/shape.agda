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

  𝕚 : Shape -- interval shape

𝕀 = ⟨ 𝕚 ⟩

postulate -- interval endpoints
  𝕚0 : 𝕀
  𝕚1 : 𝕀
  0≠1   : ∀ {ℓ} {A : Set ℓ} → 𝕚0 ≡ 𝕚1 → A

----------------------------------------------------------------------
-- Notation for interval endpoints
----------------------------------------------------------------------

open import Agda.Builtin.Nat

fromNat : Nat → 𝕀
fromNat 0 = 𝕚0
fromNat (suc _) = 𝕚1

{-# BUILTIN FROMNAT fromNat #-}

----------------------------------------------------------------------
-- The objects of shapes and shape morphisms are discrete (i.e., crisp)
----------------------------------------------------------------------
postulate
  ShapeIsDiscrete : ∀ {ℓ} {A : Shape → Set ℓ}
    → ((@♭ S : Shape) → A S) → ((S : Shape) → A S)

  ShapeIsDiscrete-β : ∀ {ℓ} {A : Shape → Set ℓ} (f : (@♭ S : Shape) → A S)
    (@♭ S : Shape) → ShapeIsDiscrete f S ≡ f S

  {-# REWRITE ShapeIsDiscrete-β #-}

  ShapeHomIsDiscrete : ∀ {ℓ} {@♭ S T : Shape} {A : ShapeHom S T → Set ℓ}
    → ((@♭ σ : ShapeHom S T) → A σ) → ((σ : ShapeHom S T) → A σ)

  ShapeHomIsDiscrete-β : ∀ {ℓ} {@♭ S T : Shape} {A : ShapeHom S T → Set ℓ}
    (f : (@♭ σ : ShapeHom S T) → A σ)
    (@♭ σ : ShapeHom S T) → ShapeHomIsDiscrete f σ ≡ f σ

  {-# REWRITE ShapeHomIsDiscrete-β #-}
