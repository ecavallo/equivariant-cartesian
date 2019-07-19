{-

Universe of fibrant types

-}
{-# OPTIONS --rewriting #-}
module universe where

open import prelude
open import shape
open import cofprop
open import fibrations
open import Data.functions
open import Data.paths
open import Data.products
open import equivs
open import glueing
open import union

postulate
  idˢ : {S : Shape} → ShapeHom S S
  ⟪idˢ⟫ : {S : Shape} → ⟪ idˢ {S = S} ⟫ ≡ id

  _∘ˢ_ : {S T V : Shape} → ShapeHom T V → ShapeHom S T → ShapeHom S V
  ⟪∘ˢ⟫ : {S T V : Shape} (τ : ShapeHom T V) (σ : ShapeHom S T) → ⟪ τ ∘ˢ σ ⟫ ≡ ⟪ τ ⟫ ∘ ⟪ σ ⟫

  ∘ˢidˢ : {S T : Shape} (σ : ShapeHom S T) → σ ∘ˢ idˢ ≡ σ
  idˢ∘ˢ : {S T : Shape} (σ : ShapeHom S T) → idˢ ∘ˢ σ  ≡ σ

  ∘ˢassoc : {S T V W : Shape} (ν : ShapeHom V W) (τ : ShapeHom T V) (σ : ShapeHom S T)
    → (ν ∘ˢ τ) ∘ˢ σ ≡ ν ∘ˢ (τ ∘ˢ σ)

  {-# REWRITE ⟪idˢ⟫ ⟪∘ˢ⟫ ∘ˢidˢ idˢ∘ˢ #-}

module Tiny (@♭ S : Shape) where

  postulate
    -- the value of the right adjoint on objects
    √ : {@♭ ℓ : Level} (@♭ A : Set ℓ) → Set ℓ

  module _ {@♭ ℓ ℓ' : Level} {@♭ A : Set ℓ} {@♭ B : Set ℓ'} where

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
    R℘ : {@♭ ℓ ℓ' ℓ'' : Level}
      {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
      (@♭ g : A → B) (@♭ f : (⟨ S ⟩ → B) → C)
      → R (f ∘ (_∘_ g)) ≡ R f ∘ g

  -- One-sided naturality of left transposition is derivable
  L℘ : {@♭ ℓ ℓ' ℓ'' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ f : B → √ C) (@♭ g : A → B)
    →  L f ∘ _∘_ g ≡ L (f ∘ g)
  L℘ f g = cong L (R℘ g (L f))

  -- Functoriality of √ in the set argument
  √` : {@♭ ℓ ℓ' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ f : A → B) → √ A → √ B
  √` f = R (f ∘ L id)

  -- The other naturality property of right transposition
  √R : {@♭ ℓ ℓ' ℓ'' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ g : B → C) (@♭ f : (⟨ S ⟩ → A) → B)
    → √` g ∘ R f ≡ R (g ∘ f)
  √R {A = A} {B} {C = C} g f =
    trans
      (cong (R ∘ _∘_ g) (L℘ id (R f)))
      (symm (R℘ (R f) (g ∘ L id)))
  -- The other naturality property of left transposition
  L√ : {@♭ ℓ ℓ' ℓ'' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ g : B → C) (@♭ f : A → √ B)
    → ---------------------
    g ∘ L f  ≡ L (√` g ∘ f)
  L√ g f = cong L (symm (√R g (L f)))

open Tiny

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

-- Functoriality and naturality in the shape argument
module _ {@♭ S T : Shape} (@♭ σ : ShapeHom S T) where

  √ShapeHom : {@♭ ℓ : Level} {@♭ A : Set ℓ}
    → √ S A → √ T A
  √ShapeHom = R T (L S id ∘ (_∘_ ◆ ⟪ σ ⟫))

  LShapeHom : {@♭ ℓ ℓ' : Level} {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ f : A → √ S B)
    → L T (√ShapeHom ∘ f) ≡ L S f ∘ (_∘_ ◆ ⟪ σ ⟫)
  LShapeHom f =
    trans
      (cong (_∘_ ◆ (_∘_ ◆ ⟪ σ ⟫)) (L℘ S id f))
      (symm (L℘ T √ShapeHom f))

  ShapeHomR : {@♭ ℓ ℓ' : Level} {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ g : (⟨ S ⟩ → A) → B)
    → √ShapeHom ∘ R S g ≡ R T (g ∘ (_∘_ ◆ ⟪ σ ⟫))
  ShapeHomR g =
    cong (R T) (LShapeHom (R S g))

record PSh (S : Shape) : Set₁ where
  field
    set : {T : Shape} (σ : ShapeHom T S) → Set
    mor : {V T : Shape} {σ : ShapeHom T S} (τ : ShapeHom V T)
      → set σ → set (σ ∘ˢ τ)

open PSh public

isFib' : (S : Shape) → (⟨ S ⟩ → Set) → PSh S
isFib' S A =
  record
  { set = λ {T} σ → isFib (A ∘ ⟪ σ ⟫)
  ; mor = λ τ α → reindex _ α ⟪ τ ⟫
  }

Set* : Set₁
Set* = Σ Set id

PSh* : Shape → Set₁
PSh* S = Σ P ∈ PSh S , P .set idˢ

PSh` : {S T : Shape} → ShapeHom S T → PSh T → PSh S
PSh` σ P =
  record
  { set = λ τ → P .set (σ ∘ˢ τ)
  ; mor = λ ν d → subst (P .set) (∘ˢassoc σ _ ν) (P .mor ν d)
  }

PSh*` : {S T : Shape} → ShapeHom S T → PSh* T → PSh* S
PSh*` σ (P , c) = (PSh` σ P , P .mor σ c)

pr₁ : {S : Shape} → PSh* S → PSh S
pr₁ = fst

record U : Set₁ where
  field
    El : Set
    fib : (@♭ S : Shape) → √ S (PSh* S)
    stable : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) →
      √ShapeHom σ (fib S) ≡ √` T (PSh*` σ) (fib T)
    base : (@♭ S : Shape) → √` S pr₁ (fib S) ≡ R S (isFib' S) El

open U public

pr₁Lfib : (@♭ S : Shape) → pr₁ ∘ L S (λ A → A .fib S) ≡ isFib' S ∘ (_∘_ El)
pr₁Lfib S =
  trans
    (cong (L S)
      (trans
        (symm (R℘ S El (isFib' S)))
        (funext (λ A → A .base S))))
    (L√ S pr₁ (λ A → A .fib S))

υ : isFib El
υ .lift =
  ShapeIsDiscrete λ (@♭ S) →
  λ r p →
  subst (λ P → P p .set idˢ)
    (pr₁Lfib S)
    (L S (λ A → A .fib S) p .snd)
    .lift S r id
υ .vary =
  ShapeIsDiscrete λ (@♭ S) →
  ShapeIsDiscrete λ (@♭ T) →
  ShapeHomIsDiscrete λ (@♭ σ) →
  λ r p φ f x₀ s →
  let
    stableLemma : PSh*` σ ∘ L T (λ A → A .fib T) ≡ L S (λ A → A .fib S) ∘ (_∘_ ◆ ⟪ σ ⟫)
    stableLemma =
      trans
        (trans
          (LShapeHom σ (λ A → A .fib S))
          (cong (L T) (symm (funext (λ A → A .stable S T σ)))))
        (L√ T (PSh*` σ) (λ A → A .fib T))
  in
  trans
    (cong
      (λ c → c .lift S r id φ (f ◇ ⟪ σ ⟫) x₀ .comp s .fst)
      (symm
        (substCongAssoc
          id
          (λ P → P (p ∘ ⟪ σ ⟫) .set idˢ)
          (pr₁Lfib S)
          (L S (λ A → A .fib S) (p ∘ ⟪ σ ⟫) .snd))))
    (trans
      (cong
        (λ c → c .lift S r id φ (f ◇ ⟪ σ ⟫) x₀ .comp s .fst)
        (trans
          (cong
            (λ {(c , eq) → coe eq (c .snd)})
            {x = _ , cong (λ P → P p .set (σ ∘ˢ idˢ)) (pr₁Lfib T)}
            {y = _ , cong (λ P → P (p ∘ ⟪ σ ⟫) .set idˢ) (pr₁Lfib S)}
            (Σext (appCong stableLemma) uipImp))
          (trans
            (substCongAssoc
              id
              (λ P → P p .set (σ ∘ˢ idˢ))
              (pr₁Lfib T)
              (PSh*` σ (L T (λ A → A .fib T) p) .snd))
            (substNaturality
              (λ P → P p .set idˢ)
              (λ P → P p .set (σ ∘ˢ idˢ))
              (λ P t → PSh*` σ (P p , t) .snd)
              (pr₁Lfib T)
              ((L T (λ A → A .fib T) p) .snd)))))
      (subst (λ P → P p .set idˢ) (pr₁Lfib T)
        (L T (λ A → A .fib T) p .snd)
        .vary S T σ r id φ f x₀ s))

decode : ∀ {ℓ} {Γ : Set ℓ} → (Γ → U) → Fib Γ
decode = reindex' (El , υ)
