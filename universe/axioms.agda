{-

Axioms used to construct a universe,
along with some immediate consequences

-}
{-# OPTIONS --rewriting #-}
module universe.axioms where

open import prelude
open import shape
open import cofprop

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

----------------------------------------------------------------------
-- Each shape is tiny (exponentiation by it has a right adjoint)
----------------------------------------------------------------------
module Tiny (@♭ S : Shape) where

  postulate
    -- the value of the right adjoint on objects
    √ : ∀ {@♭ ℓ} (@♭ A : Set ℓ) → Set ℓ

  module _ {@♭ ℓ ℓ'} {@♭ A : Set ℓ} {@♭ B : Set ℓ'} where

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
      {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
      (@♭ g : A → B) (@♭ f : (⟨ S ⟩ → B) → C)
      → R (f ∘ (_∘_ g)) ≡ R f ∘ g

  -- One-sided naturality of left transposition is derivable
  L℘ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ f : B → √ C) (@♭ g : A → B)
    →  L f ∘ _∘_ g ≡ L (f ∘ g)
  L℘ f g = cong L (R℘ g (L f))

  -- Functoriality of √ in the set argument
  √` : ∀ {@♭ ℓ ℓ'}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ f : A → B) → √ A → √ B
  √` f = R (f ∘ L id)

  -- The other naturality property of right transposition
  √R : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ g : B → C) (@♭ f : (⟨ S ⟩ → A) → B)
    → √` g ∘ R f ≡ R (g ∘ f)
  √R {A = A} {B} {C = C} g f =
    trans
      (cong (R ∘ _∘_ g) (L℘ id (R f)))
      (symm (R℘ (R f) (g ∘ L id)))
  -- The other naturality property of left transposition
  L√ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ g : B → C) (@♭ f : A → √ B)
    → ---------------------
    g ∘ L f  ≡ L (√` g ∘ f)
  L√ g f = cong L (symm (√R g (L f)))

open Tiny

-- Functoriality and naturality in the shape argument
module _ {@♭ S T : Shape} (@♭ σ : ShapeHom S T) where

  √ShapeHom : ∀ {@♭ ℓ} {@♭ A : Set ℓ}
    → √ S A → √ T A
  √ShapeHom = R T (L S id ∘ (_∘_ ◆ ⟪ σ ⟫))

  LShapeHom : ∀ {@♭ ℓ ℓ'} {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ f : A → √ S B)
    → L T (√ShapeHom ∘ f) ≡ L S f ∘ (_∘_ ◆ ⟪ σ ⟫)
  LShapeHom f =
    trans
      (cong (_∘_ ◆ (_∘_ ◆ ⟪ σ ⟫)) (L℘ S id f))
      (symm (L℘ T √ShapeHom f))

  ShapeHomR : ∀ {@♭ ℓ ℓ'} {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ g : (⟨ S ⟩ → A) → B)
    → √ShapeHom ∘ R S g ≡ R T (g ∘ (_∘_ ◆ ⟪ σ ⟫))
  ShapeHomR g =
    cong (R T) (LShapeHom (R S g))
