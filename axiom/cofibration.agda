{-

Axiomatization of the type of cofibrations.

-}
module axiom.cofibration where

open import prelude
open import axiom.funext
open import axiom.truncation
open import axiom.shape

infixr 4 _∨_

------------------------------------------------------------------------------------------
-- Axiomatization of cofibration classifier
------------------------------------------------------------------------------------------

postulate
  --↓ Object of cofibrations and decoding of cofibrations as types.
  --↓ The projection fst : Σ Cof [_] → Cof is the classifying map for cofibrations.

  Cof : Type
  [_] : Cof → Type

  --↓ The type of equalities between two elements of a shape is coded by a cofibration.

  _∋_≈_ : (S : Shape) → ⟨ S ⟩ → ⟨ S ⟩ → Cof
  [≈] : (S : Shape) (s t : ⟨ S ⟩) → [ S ∋ s ≈ t ] ≡ (s ≡ t)

  --↓ The empty type is coded by a cofibration.
  --↓ It is not strictly necessary to assume this separately: we have already assumed an
  --↓ interval shape with two disequal elements, so we could define ⊥ to be 𝕚 ∋ 0 ≈ 1.

  ⊥ : Cof
  [⊥] : [ ⊥ ] ≡ 𝟘

  --↓ The union of two cofibrations is again cofibration.

  _∨_ : Cof → Cof → Cof
  [∨] : ∀ φ ψ → [ φ ∨ ψ ] ≡ ∥ [ φ ] ⊎ [ ψ ] ∥

  --↓ Cofibrations are closed under universal quantification over a shape.

  all : (S : Shape) → (⟨ S ⟩ → Cof) → Cof
  [all] : ∀ S φ → [ all S φ ] ≡ ((s : ⟨ S ⟩) → [ φ s ])

  --↓ Any cofibration is a proposition (up to strict equality).

  cofIsProp : (φ : Cof) → isProp [ φ ]

  --↓ The shape equality and univeral quantification cofibrations are invariant under
  --↓ shape morphisms in an appropriate sense.

  --↓ The first axiom can be understood as asserting that shape morphisms are monic.

  ≈Equivariant : {S T : Shape} (σ : ShapeHom S T) (r s : ⟨ S ⟩)
    → (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (S ∋ r ≈ s)

  --↓ The second axiom can be understood as asserting that shape morphisms are epic as
  --↓ seen by cofibrations. It is used in the proof of realignment for fibrations.

  allEquivariant : {S T : Shape} (σ : ShapeHom S T) (φ : ⟨ T ⟩ → Cof)
    → all T φ ≡ all S (φ ∘ ⟪ σ ⟫)

--↓ For convenience, we make the equations decoding cofibrations into definitional
--↓ equalities using a REWRITE pragma.

{-# REWRITE [≈] [⊥] [∨] [all] #-}
