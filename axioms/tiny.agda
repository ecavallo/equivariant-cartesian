{-

Tinyness of shapes. These axioms are only used for the universe.

-}
{-# OPTIONS --rewriting #-}
module axioms.tiny where

open import prelude
open import axioms.funext
open import axioms.truncation
open import axioms.shape
open import axioms.cofprop

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
shape→⊎♭ : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
  → ((⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) ≅ (⟨ S ⟩ → A ⊎ B)
shape→⊎♭ S {A} {B} =
  record
  { to = forward
  ; from = L S back
  ; inv₁ = funext back∘forward
  ; inv₂ = trans (cong (L S) (funext forward∘back)) (L√ S forward back)
  }
  where
  forward = [ _∘_ inl ∣ _∘_ inr ]
  back = [ R S inl ∣ R S inr ]

  forward∘back : (c : A ⊎ B) → √` S forward (back c) ≡ R S id c
  forward∘back (inl a) = appCong (trans (R℘ S inl id) (√R S forward inl))
  forward∘back (inr b) = appCong (trans (R℘ S inr id) (√R S forward inr))

  back∘forward : (d : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) → L S back (forward d) ≡ d
  back∘forward (inl f) = appCong (L℘ S back inl)
  back∘forward (inr g) = appCong (L℘ S back inr)

shape→⊎♭` : ∀ {@♭ ℓ ℓ' ℓ'' ℓ'''} (@♭ S : Shape)
    {@♭ A : Set ℓ} {@♭ A' : Set ℓ'}
    {@♭ B : Set ℓ''} {@♭ B' : Set ℓ'''}
    (f : A → A') (g : B → B')
    (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B))
    → shape→⊎♭ S .to ((_∘_ f ⊎` _∘_ g) p) ≡ (f ⊎` g) ∘ (shape→⊎♭ S .to p)
shape→⊎♭` S f g (inl _) = refl
shape→⊎♭` S f g (inr _) = refl

shape→⊎♭∇ : ∀ {@♭ ℓ} (@♭ S : Shape) {@♭ A : Set ℓ}
  (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → A))
  → ∇ ∘ shape→⊎♭ S .to p ≡ ∇ p
shape→⊎♭∇ S (inl _) = refl
shape→⊎♭∇ S (inr _) = refl

shape→⊎ : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape)
  {A : ⟨ S ⟩ → Set ℓ} {B : ⟨ S ⟩ → Set ℓ'}
  → ((s : ⟨ S ⟩) → A s ⊎ B s) → Π A ⊎ Π B
shape→⊎ {ℓ} {ℓ'} S {A} {B} h = main
  where
  Setₗ = Σ AB ∈ Set ℓ × Set ℓ' , AB .fst
  Setᵣ = Σ AB ∈ Set ℓ × Set ℓ' , AB .snd

  iso = shape→⊎♭ S

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
        (cong (iso .from) (shape→⊎♭` S fst fst (iso .from h'))))
      (symm (appCong (iso .inv₁)))

  baseEq : ∇ ((_∘_ fst ⊎` _∘_ fst) (shape→⊎♭ S .from h')) ≡ AB
  baseEq =
    trans
      (trans
        (trans
          (funext fsth')
          (cong (_∘_ ∇) (appCong (iso .inv₂))))
        (symm (shape→⊎♭∇ S (iso .from ((fst ⊎` fst) ∘ h')))))
      (cong ∇ fromNatural)

  main : Π A ⊎ Π B
  main with shape→⊎♭ S .from h' | baseEq
  main | inl f | eq = inl λ s → coe (cong fst (appCong eq)) (f s .snd)
  main | inr g | eq = inr λ s → coe (cong snd (appCong eq)) (g s .snd)

-- ----------------------------------------------------------------------
-- -- In progress
-- ----------------------------------------------------------------------

-- module _ (@♭ S : Shape) where

--   record U∀ : Set₁ where
--     field
--       A : Set
--       All : √ S (Set* lzero)
--       AllBase : √` S fst All ≡ R S Π A

--   encode : (A : ⟨ S ⟩ → Set) → (s : ⟨ S ⟩) (u : A s) → U∀
--   encode =
--     λ A s u → 
--     record
--     { A = A s
--     ; All = R S al (A s , u)
--     ; AllBase = trans (appCong (R℘ S fst Π)) (appCong (√R S fst al)) }
--     where
--     al : (⟨ S ⟩ → Set* lzero) → Set* lzero
--     al Aa = (Π (fst ∘ Aa) , snd ∘ Aa)

--   decode : (C : (s : ⟨ S ⟩) → U∀) → Π (U∀.A ∘ C)
--   decode C =
--     coe
--       (appCong fstLemma)
--       (L S U∀.All C .snd)
--     where
--     fstLemma : fst ∘ L S U∀.All ≡ Π ∘ (_∘_ U∀.A)
--     fstLemma =
--       trans
--         (cong (L S)
--           (trans
--             (symm (R℘ S U∀.A Π))
--             (funext U∀.AllBase)))
--         (L√ S fst U∀.All)
