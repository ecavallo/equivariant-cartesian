{-

Axiomatization of cofibrations.

-}
module axiom.cofibration where

open import basic
open import axiom.funext
open import axiom.shape

infixr 4 _∨_

------------------------------------------------------------------------------------------
-- Axiomatization of the cofibration classifier.
------------------------------------------------------------------------------------------

postulate
  --↓ Object of cofibrations and decoding of cofibrations as types.
  --↓ The projection fst : Σ Cof [_] → Cof is the classifying map for cofibrations.

  Cof : Type
  [_] : Cof → Type

  --↓ Any cofibration is a strict proposition.

  cofIsStrictProp : (φ : Cof) → isStrictProp [ φ ]

  --↓ The type of equalities between two elements of a shape is coded by a cofibration.

  _∋_≈_ : (S : Shape) → ⟨ S ⟩ → ⟨ S ⟩ → Cof
  [≈] : (S : Shape) (s t : ⟨ S ⟩) → [ S ∋ s ≈ t ] ≡ (s ≡ t)

  --↓ The empty and unit types are coded by cofibrations.
  --↓ It is not strictly necessary to assume these separately: we have already assumed an
  --↓ interval shape with two disequal elements, so we could define ⊥ to be 𝕚 ∋ 0 ≈ 1 and
  --↓ ⊤ to be 𝕚 ∋ 0 ≈ 0.

  ⊥ : Cof
  [⊥] : [ ⊥ ] ≡ 𝟘

  ⊤ : Cof
  [⊤] : [ ⊤ ] ≡ 𝟙

  --↓ The union of two cofibrations is again a cofibration. Rather than introducing an
  --↓ equality for decoding the union of cofibrations, we axiomatize its introduction
  --↓ and elimination principles directly.

  _∨_ : Cof → Cof → Cof

  ∨l : {φ ψ : Cof} → [ φ ] → [ φ ∨ ψ ]
  ∨r : {φ ψ : Cof} → [ ψ ] → [ φ ∨ ψ ]

  ∨-elim : ∀ {ℓ} {φ ψ : Cof} {P : [ φ ∨ ψ ] → Type ℓ}
    (f : (u : [ φ ]) → P (∨l u))
    (g : (v : [ ψ ]) → P (∨r v))
    (p : (u : [ φ ]) (v : [ ψ ]) → subst P (cofIsStrictProp (φ ∨ ψ) _ _) (f u) ≡ g v)
    (w : [ φ ∨ ψ ]) → P w

  ∨-elim-βl : ∀ ℓ φ ψ P f g p u → ∨-elim {ℓ} {φ} {ψ} {P} f g p (∨l u) ≡ f u
  ∨-elim-βr : ∀ ℓ φ ψ P f g p v → ∨-elim {ℓ} {φ} {ψ} {P} f g p (∨r v) ≡ g v

  --↓ Cofibrations are closed under universal quantification over a shape.

  all : (S : Shape) → (⟨ S ⟩ → Cof) → Cof
  [all] : ∀ S φ → [ all S φ ] ≡ ((s : ⟨ S ⟩) → [ φ s ])

  --↓ We require that the shape equality and universal quantification cofibrations are
  --↓ invariant under shape morphisms in the following sense.

  --↓ The first axiom can be read as asserting that shape morphisms are monic.

  ≈Equivariant : {S T : Shape} (σ : Shape[ S , T ]) (r s : ⟨ S ⟩)
    → (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (S ∋ r ≈ s)

  --↓ The second axiom can be understood as asserting that shape morphisms are epic as
  --↓ far as cofibrations can see. It is used in the proof of realignment for fibrations.

  allEquivariant : {S T : Shape} (σ : Shape[ S , T ]) (φ : ⟨ T ⟩ → Cof)
    → all T φ ≡ all S (φ ∘ ⟪ σ ⟫)

--↓ For convenience, we make the equations decoding cofibrations into definitional
--↓ equalities using a REWRITE pragma.

{-# REWRITE [≈] [⊥] [⊤] ∨-elim-βl ∨-elim-βr [all] #-}
