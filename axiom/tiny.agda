{-

Axioms requiring that each shape is tiny, in the sense that exponentiation by each shape
has an external right adjoint.

The fact that this right adjoint is external is captured by its being a flat-modal
function from the universe of types. In the motivating semantics in cartesian cubical
sets, this means it takes a closed presheaf as an argument rather than a family of
presheaves over a context. (More precisely, it takes a family of presheaves over a *set*
as opposed to over an arbitrary *presheaf*.)

We encode the adjunction as a natural isomorphism on hom-sets.

-}
module axiom.tiny where

open import basic
open import axiom.shape

infixr 4 _√_

--↓ The right adjoint to exponentiation by S, written S √ (–)

postulate
  _√_ : ∀ {@♭ ℓ} (@♭ S : Shape) (@♭ A : Type ℓ) → Type ℓ

module √Axioms (@♭ S : Shape) where

  module _ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'} where

    postulate
      --↓ Transposition from left to right.

      transposeRight : @♭ (A ^ S → B) → (A → S √ B)

      --↓ Transposition from right to left.

      transposeLeft : @♭ (A → S √ B) → (A ^ S → B)

      --↓ Right and left transposition are mutually inverse.

      transposeLeftRight : (@♭ f : A ^ S → B) → transposeLeft (transposeRight f) ≡ f
      transposeRightLeft : (@♭ g : A → S √ B) → transposeRight (transposeLeft g) ≡ g

    {-# REWRITE transposeLeftRight transposeRightLeft #-}

  postulate
    --↓ Naturality of left-to-right transposition in the domain.

    transposeRight^ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
      (@♭ h : A → A') (@♭ f : A' ^ S → B)
      → transposeRight (f ∘ (h `^ S)) ≡ transposeRight f ∘ h
