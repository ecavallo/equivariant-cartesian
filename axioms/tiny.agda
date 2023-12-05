{-

Tinyness of shapes. These axioms are only used for the universe.

-}
module axioms.tiny where

open import prelude
open import axioms.funext
open import axioms.truncation
open import axioms.shape
open import axioms.cofibration

------------------------------------------------------------------------------------------
-- Each shape is tiny (exponentiation by it has a right adjoint)
------------------------------------------------------------------------------------------

module Tiny (@♭ S : Shape) where

  postulate
    -- the value of the right adjoint on objects
    √ : ∀ {@♭ ℓ} (@♭ A : Type ℓ) → Type ℓ

  module _ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'} where

    postulate
      -- right transposition across the adjunction
      R : @♭ ((⟨ S ⟩ → A) → B) → (A → √ B)

      -- left transposition across the adjunction
      L : @♭ (A → √ B) → ((⟨ S ⟩ → A) → B)

      -- right and left transposition are mutually inverse
      LR : (@♭ f : (⟨ S ⟩ → A) → B) → L (R f) ≡ f
      RL : (@♭ g : A → √ B) → R (L g) ≡ g

    {-# REWRITE LR RL #-}

  postulate
    -- one-sided naturality of right transposition
    R℘ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
      (@♭ g : A → B) (@♭ f : (⟨ S ⟩ → B) → C)
      → R (f ∘ (g ∘_)) ≡ R f ∘ g

  -- One-sided naturality of left transposition is derivable
  L℘ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ f : B → √ C) (@♭ g : A → B)
    → L f ∘ (g ∘_) ≡ L (f ∘ g)
  L℘ f g = cong♭ L (R℘ g (L f))

  -- Functoriality of √ in the set argument
  √` : ∀ {@♭ ℓ ℓ'}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ f : A → B) → √ A → √ B
  √` f = R (f ∘ L id)

  -- The other naturality property of right transposition
  √R : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ g : B → C) (@♭ f : (⟨ S ⟩ → A) → B)
    → √` g ∘ R f ≡ R (g ∘ f)
  √R {A = A} {B} {C = C} g f =
    sym (R℘ (R f) (g ∘ L id))
    ∙ cong♭ (λ h → R (g ∘ h)) (L℘ id (R f))
  -- The other naturality property of left transposition
  L√ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ g : B → C) (@♭ f : A → √ B)
    → g ∘ L f  ≡ L (√` g ∘ f)
  L√ g f = cong♭ L (sym (√R g (L f)))

open Tiny

-- Functoriality and naturality in the shape argument
module _ {@♭ S T : Shape} (@♭ σ : ShapeHom S T) where

  √ShapeHom : ∀ {@♭ ℓ} {@♭ A : Type ℓ}
    → √ S A → √ T A
  √ShapeHom = R T (L S id ∘ (_∘ ⟪ σ ⟫))

  LShapeHom : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ f : A → √ S B)
    → L T (√ShapeHom ∘ f) ≡ L S f ∘ (_∘ ⟪ σ ⟫)
  LShapeHom f =
    sym (L℘ T √ShapeHom f)
    ∙ cong (_∘ (_∘ ⟪ σ ⟫)) (L℘ S id f)

  ShapeHomR : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ g : (⟨ S ⟩ → A) → B)
    → √ShapeHom ∘ R S g ≡ R T (g ∘ (_∘ ⟪ σ ⟫))
  ShapeHomR g =
    cong♭ (R T) (LShapeHom (R S g))
