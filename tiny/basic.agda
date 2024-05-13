{-

Basic consequences of the axiomatized right adjoint to exponentation by a shape.

-}
module tiny.basic where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration
open import axiom.tiny

module Tiny (@♭ S : Shape) where

  open √Axioms S public

  --↓ Functoriality of √ in the type argument.

  √` : ∀ {@♭ ℓ ℓ'}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ h : A → B) → S √ A → S √ B
  √` h = transposeRight (h ∘ transposeLeft id)

  --↓ Naturality of right-to-left transposition in the domain.

  transposeLeft^ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
    (@♭ g : A' → S √ B) (@♭ h : A → A')
    → transposeLeft g ∘ (h `^ S) ≡ transposeLeft (g ∘ h)
  transposeLeft^ g h = cong♭ transposeLeft (transposeRight^ h (transposeLeft g))

  --↓ Naturality of left-to-right transposition in the codomain.

  √TransposeRight : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ f : A ^ S → B)
    → √` h ∘ transposeRight f ≡ transposeRight (h ∘ f)
  √TransposeRight h f =
    sym (transposeRight^ (transposeRight f) (h ∘ transposeLeft id))
    ∙ cong♭ (λ f' → transposeRight (h ∘ f')) (transposeLeft^ id (transposeRight f))

  --↓ Naturality of right-to-left transposition in the codomain.

  √TransposeLeft : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ g : A → S √ B)
    → h ∘ transposeLeft g ≡ transposeLeft (√` h ∘ g)
  √TransposeLeft h g = cong♭ transposeLeft (sym (√TransposeRight h (transposeLeft g)))
