{-

Axiomatization of cofibrations.

-}
module axiom.cofibration where

open import basic
open import axiom.funext
open import axiom.shape

infixr 4 _∨_

postulate
  --↓ We postulate a type of cofibrations and decoding of cofibrations as types.
  --↓ The projection fst : Σ Cof [_] → Cof is the classifying map for cofibrations.

  --↓ In the motivating semantics in cartesian cubical sets, the type of cofibrations is
  --↓ the subobject classifier, or the classifier for levelwise decidable subobjects if
  --↓ working constructively.

  Cof : Type
  [_] : Cof → Type

  --↓ We postulate that each cofibration is a proposition of the ambient type theory.

  cofIsStrictProp : (φ : Cof) → isStrictProp [ φ ]

  --↓ We postulate that the type of equalities between two elements of a shape is coded by
  --↓ a cofibration.

  _∋_≈_ : (S : Shape) → ⟨ S ⟩ → ⟨ S ⟩ → Cof
  [≈] : (S : Shape) (s t : ⟨ S ⟩) → [ S ∋ s ≈ t ] ≡ (s ≡ t)

  --↓ We postulate that the empty and unit types are coded by cofibrations.
  --↓ These postulates are redundant: we have already assumed an interval shape with two
  --↓ distinct elements, so we could define ⊥ to be 𝕚 ∋ 0 ≈ 1 and ⊤ to be 𝕚 ∋ 0 ≈ 0.
  --↓ It is however convenient to take them as primitive.

  ⊥ : Cof
  [⊥] : [ ⊥ ] ≡ 𝟘

  ⊤ : Cof
  [⊤] : [ ⊤ ] ≡ 𝟙

  --↓ We postulate that the union of two cofibrations is again a cofibration.
  --↓ Rather than postulating the existence of the union of arbitrary propositions (e.g.
  --↓ via propositional truncation) and asserting a decoding equality for ∨, we axiomatize
  --↓ introduction and elimination rules for the decoding of ∨ directly.

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

  --↓ We postulate that cofibrations are closed under universal quantification over a shape.

  all : (S : Shape) → (⟨ S ⟩ → Cof) → Cof
  [all] : ∀ S φ → [ all S φ ] ≡ ((s : ⟨ S ⟩) → [ φ s ])

  --↓ We postulate that the shape equality and universal quantification cofibrations are
  --↓ invariant under shape morphisms in the following sense. These axioms have the effect
  --↓ of forcing shape morphisms to be isomorphism-like, and are in particular
  --↓ automatically satisfied if all shape morphisms are isomorphisms and Cof is
  --↓ extensional (logically equivalent cofibrations are equal), as is the case in the
  --↓ motivating semantics.

  --↓ We postulate that shape equality is invariant under shape morphisms.
  --↓ This can be read as asserting that shape morphisms are monic.

  ≈Equivariant : {S T : Shape} (σ : Shape[ S , T ]) (r s : ⟨ S ⟩)
    → (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (S ∋ r ≈ s)

  --↓ We postulate that universal quantification is invariant under shape morphisms.
  --↓ This can be read as asserting that shape morphisms are epic from the perspective of
  --↓ cofibrations.

  allEquivariant : {S T : Shape} (σ : Shape[ S , T ]) (φ : ⟨ T ⟩ → Cof)
    → all T φ ≡ all S (φ ∘ ⟪ σ ⟫)

--↓ For convenience, we make the equations decoding cofibrations into definitional
--↓ equalities using a REWRITE pragma.

{-# REWRITE [≈] [⊥] [⊤] ∨-elim-βl ∨-elim-βr [all] #-}
