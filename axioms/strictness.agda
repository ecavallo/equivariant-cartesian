{-

Po

Axioms related to strictifying Glue types.

-}
{-# OPTIONS --rewriting #-}
module axioms.strictness where

open import prelude
open import axioms.cofprop

----------------------------------------------------------------------
-- Strictifying
----------------------------------------------------------------------
postulate
 reIm : ∀ {ℓ}
  (φ : CofProp)
  (A : [ φ ] → Set ℓ)
  (B : Set ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  → ----------------------
  Σ B' ∈ Set ℓ , Σ m' ∈ B' ≅ B , ((u : [ φ ]) → (A u , m u) ≡ (B' , m'))

strictify : ∀ {ℓ}
  (φ : CofProp)
  (A : [ φ ] → Set ℓ)
  (B : Set ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  → ----------------------
  Set ℓ
strictify φ A B m = reIm φ A B m .fst

isoB : ∀ {ℓ}
  (φ : CofProp)
  (A : [ φ ] → Set ℓ)
  (B : Set ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  → ----------------------
  strictify φ A B m ≅ B
isoB φ A B m = reIm φ A B m .snd .fst

restrictsToA : ∀ {ℓ}
  (φ : CofProp)
  (A : [ φ ] → Set ℓ)
  (B : Set ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  (u : [ φ ])
  → ----------------------
  A u ≡ strictify φ A B m
restrictsToA φ A B m u = cong fst (reIm φ A B m .snd .snd u)

restrictsToM : ∀ {ℓ}
  (φ : CofProp)
  (A : [ φ ] → Set ℓ)
  (B : Set ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  (u : [ φ ])
  → ----------------------
  (A u , m u) ≡ (strictify φ A B m , isoB φ A B m)
restrictsToM φ A B m u = reIm φ A B m .snd .snd u
