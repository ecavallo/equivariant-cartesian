{-

Tinyness of shapes. These axioms are only used for the universe.

-}
{-# OPTIONS --rewriting #-}
module axioms.tiny where

open import prelude
open import axioms.funext
open import axioms.shape

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

----------------------------------------------------------------------
-- (Dependent) exponentiation by a shape commutes with coproducts
----------------------------------------------------------------------

Shape→⊎♭ : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
  → ((⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) ≅ (⟨ S ⟩ → A ⊎ B)
Shape→⊎♭ S {A} {B} =
  record
  { to = forward
  ; from = L S back
  ; inv₁ = funext back∘forward
  ; inv₂ = trans (cong (L S) (funext forward∘back)) (L√ S forward back)
  }
  where
  forward = [ _∘_ inl , _∘_ inr ]
  back = [ R S inl , R S inr ]

  forward∘back : (c : A ⊎ B) → √` S forward (back c) ≡ R S id c
  forward∘back (inl a) = appCong (trans (R℘ S inl id) (√R S forward inl))
  forward∘back (inr b) = appCong (trans (R℘ S inr id) (√R S forward inr))

  back∘forward : (d : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) → L S back (forward d) ≡ d
  back∘forward (inl f) = appCong (L℘ S back inl)
  back∘forward (inr g) = appCong (L℘ S back inr)

Shape→⊎♭` : ∀ {@♭ ℓ ℓ' ℓ'' ℓ'''} (@♭ S : Shape)
    {@♭ A : Set ℓ} {@♭ A' : Set ℓ'}
    {@♭ B : Set ℓ''} {@♭ B' : Set ℓ'''}
    (f : A → A') (g : B → B')
    (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B))
    → Shape→⊎♭ S .to ((_∘_ f ⊎` _∘_ g) p) ≡ (f ⊎` g) ∘ (Shape→⊎♭ S .to p)
Shape→⊎♭` S f g (inl _) = refl
Shape→⊎♭` S f g (inr _) = refl

Shape→⊎♭∇ : ∀ {@♭ ℓ} (@♭ S : Shape) {@♭ A : Set ℓ}
  (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → A))
  → ∇ ∘ Shape→⊎♭ S .to p ≡ ∇ p
Shape→⊎♭∇ S (inl _) = refl
Shape→⊎♭∇ S (inr _) = refl

Shape→⊎ : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape)
  {A : ⟨ S ⟩ → Set ℓ} {B : ⟨ S ⟩ → Set ℓ'}
  → ((s : ⟨ S ⟩) → A s ⊎ B s) → Π A ⊎ Π B
Shape→⊎ {ℓ} {ℓ'} S {A} {B} h = main
  where
  Setₗ = Σ AB ∈ Set ℓ × Set ℓ' , AB .fst
  Setᵣ = Σ AB ∈ Set ℓ × Set ℓ' , AB .snd

  iso = Shape→⊎♭ S

  AB : ⟨ S ⟩ → Set ℓ × Set ℓ'
  AB s = (A s , B s)

  h' : ⟨ S ⟩ → Setₗ ⊎ Setᵣ
  h' s = ((_,_ (AB s)) ⊎` (_,_ (AB s))) (h s)

  fsth' : ∀ s → ∇ ((fst ⊎` fst) (h' s)) ≡ AB s
  fsth' s with h s
  fsth' s | inl _ = refl
  fsth' s | inr _ = refl

  fromNatural : (_∘_ fst ⊎` _∘_ fst) (iso .from h') ≡ iso .from ((fst ⊎` fst) ∘ h')
  fromNatural =
    trans
      (trans
        (cong (iso .from ∘ _∘_ (fst ⊎` fst)) (appCong (iso .inv₂)))
        (cong (iso .from) (Shape→⊎♭` S fst fst (iso .from h'))))
      (symm (appCong (iso .inv₁)))

  baseEq : ∇ ((_∘_ fst ⊎` _∘_ fst) (Shape→⊎♭ S .from h')) ≡ AB
  baseEq =
    trans
      (trans
        (trans
          (funext fsth')
          (cong (_∘_ ∇) (appCong (iso .inv₂))))
        (symm (Shape→⊎♭∇ S (iso .from ((fst ⊎` fst) ∘ h')))))
      (cong ∇ fromNatural)

  main : Π A ⊎ Π B
  main with Shape→⊎♭ S .from h' | baseEq
  main | inl f | eq = inl λ s → coe (cong fst (appCong eq)) (f s .snd)
  main | inr g | eq = inr λ s → coe (cong snd (appCong eq)) (g s .snd)
