{-

Axiomatization of fibrant replacement of a map π : A → Γ by a fibration Γ → Type,

Fibrant replacement is not used in the main development, but would be necessary to
interpret higher inductive types, so we demonstrate here that fibrant replacement for
equivariant fibrations is definable as a (recursive) indexed quotient inductive type
(QIT).

Unlike fibration replacement for the non-equivariant cartesian cubical set model, it
seems that equivariant fibrant replacment is not an instance of Swan's W-types with
reductions as defined in:

  Swan
  W-Types with Reductions and the Small Object Argument
  https://arxiv.org/abs/1802.07588

The equivariant fibrant replacement of a map π : A → Γ can however still be expressed as
a QIT indexed by Γ; we axiomatize this QIT here.

-}
module axiom.fibrant-replacement where

open import basic
open import axiom.shape
open import cofibration
open import fibration.fibration

private variable
  ℓ ℓ' ℓ'' : Level
  Γ : Type ℓ

module _ {ℓ ℓ'} {A : Type ℓ} {Γ : Type ℓ'} (π : A → Γ) where

  postulate
    --↓ Fibrant replacement of π : A → Γ as a family over Γ.

    FibReplace : Γ → Type (ℓ ⊔ ℓ')

    --↓ Map from the input to its fibrant replacement.

    infr : (a : A) → FibReplace (π a)

    --↓ Every open box in the fibrant replacement has a filler.

    liftfr :
      (S : Shape)
      (p : Γ ^ S)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (s : ⟨ S ⟩)
      → FibReplace (p s)

    --↓ Equation stating that fillers fill the open boxes they are meant to fill.

    matchfr :
      (S : Shape)
      (p : Γ ^ S)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (s : ⟨ S ⟩)
      (u : [ φ ∨ S ∋ r ≈ s ])
      → part s u
        ≡ liftfr S p r φ part s

    --↓ Equation stating that fillers satisfy the equivariance condition.

    varyfr :
      (S : Shape) (T : Shape) (σ : Shape[ S , T ])
      (p : Γ ^ T)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (j : ⟨ T ⟩) → [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ] → FibReplace (p j))
      (s : ⟨ S ⟩)
      → liftfr T p (⟪ σ ⟫ r) φ part (⟪ σ ⟫ s)
        ≡ liftfr S (p ∘ ⟪ σ ⟫) r φ (reshapePartial σ part) s

  {-# REWRITE varyfr #-}

  module _ {P : (γ : Γ) → FibReplace γ → Type ℓ''}
    (infr* : (a : A) → P (π a) (infr a))
    (liftfr* :
      (S : Shape)
      (p : Γ ^ S)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (part* : (i : ⟨ S ⟩) (u : [ φ ∨ S ∋ r ≈ i ]) → P (p i) (part i u))
      (s : ⟨ S ⟩)
      → P (p s) (liftfr S p r φ part s))
    (matchfr* :
      (S : Shape)
      (p : Γ ^ S)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (part* : (i : ⟨ S ⟩) (u : [ φ ∨ S ∋ r ≈ i ]) → P (p i) (part i u))
      (s : ⟨ S ⟩)
      (u : [ φ ∨ S ∋ r ≈ s ])
      → subst (P (p s)) (matchfr S p r φ part s u) (part* s u)
        ≡ liftfr* S p r φ part part* s)
    (varyfr* :
      (S : Shape) (T : Shape) (σ : Shape[ S , T ])
      (p : Γ ^ T)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (j : ⟨ T ⟩) → [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ] → FibReplace (p j))
      (part* : (j : ⟨ T ⟩) (u : [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ]) → P (p j) (part j u))
      (s : ⟨ S ⟩)
      → liftfr* T p (⟪ σ ⟫ r) φ part part* (⟪ σ ⟫ s)
        ≡ liftfr* S (p ∘ ⟪ σ ⟫) r φ (reshapePartial σ part) (reshapePartial σ part*) s)
    where

    postulate
      --↓ Eliminator for the fibrant replacement.

      FibReplace-elim : (γ : Γ) (t : FibReplace γ) → P γ t

      --↓ Computation rule for elements from the input map.

      FibReplace-elim-β-in : (a : A) → FibReplace-elim (π a) (infr a) ≡ infr* a

      --↓ Computation rule for freely-added lifts.

      FibReplace-elim-β-lift :
        (S : Shape)
        (p : Γ ^ S)
        (r : ⟨ S ⟩)
        (φ : Cof)
        (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
        (s : ⟨ S ⟩)
        → FibReplace-elim (p s) (liftfr S p r φ part s)
          ≡ liftfr* S p r φ part (λ i u → FibReplace-elim (p i) (part i u)) s

      {-# REWRITE FibReplace-elim-β-in FibReplace-elim-β-lift #-}
