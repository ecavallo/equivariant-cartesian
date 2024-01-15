{-

Axiomatization of fibrant replacement of a map π : A → Γ by a fibration Γ → Type,
expressed as a (recursive) indexed quotient-inductive type (QIT).

Unlike fibration replacement for the non-equivariant cartesian cubical set model, it does
seems that equivariant fibrant replacment is not an instance of Swan's W-types with
reductions as defined in:

  Swan
  W-Types with Reductions and the Small Object Argument
  https://arxiv.org/abs/1802.07588

The construction of higher inductive types (which incorporates a fibrant replacement)
presented in

  Coquand, Huber, & Mörtberg
  On Higher Inductive Types in Cubical Type Theory
  https://doi.org/10.1145/3209108.3209197

likewise does not obviously adapt to equivariant fibrations.

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
    FibReplace : Γ → Type (ℓ ⊔ ℓ')

    infr : (a : A) → FibReplace (π a)

    liftfr :
      (S : Shape)
      (p : ⟨ S ⟩ → Γ)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (s : ⟨ S ⟩)
      → FibReplace (p s)

    matchfr :
      (S : Shape)
      (p : ⟨ S ⟩ → Γ)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (s : ⟨ S ⟩)
      (u : [ φ ∨ S ∋ r ≈ s ])
      → liftfr S p r φ part s
        ≡ part s u

    varyfr :
      (S : Shape) (T : Shape) (σ : ShapeHom S T)
      (p : ⟨ T ⟩ → Γ)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (j : ⟨ T ⟩) → [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ] → FibReplace (p j))
      (s : ⟨ S ⟩)
      → liftfr T p (⟪ σ ⟫ r) φ part (⟪ σ ⟫ s)
        ≡ liftfr S (p ∘ ⟪ σ ⟫) r φ (reshapePartial σ part) s

  module _ {P : (γ : Γ) → FibReplace γ → Type ℓ''}
    (infr* : (a : A) → P (π a) (infr a))
    (liftfr* :
      (S : Shape)
      (p : ⟨ S ⟩ → Γ)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (part* : (i : ⟨ S ⟩) (u : [ φ ∨ S ∋ r ≈ i ]) → P (p i) (part i u))
      (s : ⟨ S ⟩)
      → P (p s) (liftfr S p r φ part s))
    (matchfr* :
      (S : Shape)
      (p : ⟨ S ⟩ → Γ)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
      (part* : (i : ⟨ S ⟩) (u : [ φ ∨ S ∋ r ≈ i ]) → P (p i) (part i u))
      (s : ⟨ S ⟩)
      (u : [ φ ∨ S ∋ r ≈ s ])
      → subst (P (p s)) (matchfr S p r φ part s u)
          (liftfr* S p r φ part part* s)
        ≡ part* s u)
    (varyfr* :
      (S : Shape) (T : Shape) (σ : ShapeHom S T)
      (p : ⟨ T ⟩ → Γ)
      (r : ⟨ S ⟩)
      (φ : Cof)
      (part : (j : ⟨ T ⟩) → [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ] → FibReplace (p j))
      (part* : (j : ⟨ T ⟩) (u : [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ]) → P (p j) (part j u))
      (s : ⟨ S ⟩)
      → subst (P (p (⟪ σ ⟫ s))) (varyfr S T σ p r φ part s)
          (liftfr* T p (⟪ σ ⟫ r) φ part part* (⟪ σ ⟫ s))
        ≡ liftfr* S (p ∘ ⟪ σ ⟫) r φ (reshapePartial σ part) (reshapePartial σ part*) s)
    where

    postulate
      FibReplace-elim : (γ : Γ) (t : FibReplace γ) → P γ t

      FibReplace-elim-β-in : (a : A) → FibReplace-elim (π a) (infr a) ≡ infr* a

      FibReplace-elim-β-lift :
        (S : Shape)
        (p : ⟨ S ⟩ → Γ)
        (r : ⟨ S ⟩)
        (φ : Cof)
        (part : (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → FibReplace (p i))
        (s : ⟨ S ⟩)
        → FibReplace-elim (p s) (liftfr S p r φ part s)
          ≡ liftfr* S p r φ part (λ i u → FibReplace-elim (p i) (part i u)) s

      {-# REWRITE FibReplace-elim-β-in FibReplace-elim-β-lift #-}
