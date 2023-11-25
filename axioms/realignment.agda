{-

Postulates realignment for the universes of the extensional type theory.

-}
{-# OPTIONS --rewriting #-}
module axioms.realignment where

open import prelude
open import axioms.cofprop

private variable ℓ : Level

postulate
 reIm : (φ : CofProp) (A : [ φ ] → Type ℓ) (B : Type ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  → Σ B' ∈ Type ℓ , Σ m' ∈ B' ≅ B , ((u : [ φ ]) → (A u , m u) ≡ (B' , m'))

realign : (φ : CofProp) (A : [ φ ] → Type ℓ) (B : Type ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  → Type ℓ
realign φ A B m = reIm φ A B m .fst

isoB : (φ : CofProp) (A : [ φ ] → Type ℓ) (B : Type ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  → realign φ A B m ≅ B
isoB φ A B m = reIm φ A B m .snd .fst

restrictsToA : (φ : CofProp) (A : [ φ ] → Type ℓ) (B : Type ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  (u : [ φ ]) → A u ≡ realign φ A B m
restrictsToA φ A B m u = cong fst (reIm φ A B m .snd .snd u)

restrictsToM : (φ : CofProp) (A : [ φ ] → Type ℓ) (B : Type ℓ)
  (m : (u : [ φ ]) → A u ≅ B)
  (u : [ φ ]) → (A u , m u) ≡ (realign φ A B m , isoB φ A B m)
restrictsToM φ A B m u = reIm φ A B m .snd .snd u
