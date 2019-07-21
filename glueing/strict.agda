{-

Strict Glue types.

-}
{-# OPTIONS --rewriting #-}
module glueing.strict where

open import prelude
open import shape
open import cofprop
open import fibrations
open import equivs
open import Data.paths
open import Data.products
open import strictness-axioms
open import glueing.core

----------------------------------------------------------------------
-- Strict glueing
----------------------------------------------------------------------
includeA : ∀ {ℓ}
  (φ : CofProp)
  {A : [ φ ] → Set ℓ}
  {B : Set ℓ}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  (u : [ φ ]) → A u → Glue φ A B f
includeA φ {A} {B} f u a =
  glue
    (λ v → moveA v a)
    (f u a)
    (λ v → cong (λ{(u , a) → f u a}) (symm (moveMove v)))
  where
  moveA : (v : [ φ ]) → A u → A v
  moveA v = subst A (cofIsProp φ _ _)
  moveMove : (v : [ φ ]) → (u , a) ≡ (v , moveA v a)
  moveMove v = Σext (cofIsProp φ _ _) refl

includeAIso : ∀ {ℓ}
  (φ : CofProp)
  {A : [ φ ] → Set ℓ}
  {B : Set ℓ}
  (w : (u : [ φ ]) → A u → B)
  → ---------------
  (u : [ φ ]) → A u ≅ Glue φ A B w
includeAIso φ {A} {B} w u = iso
  where
  prfIr : {a : A u} → subst A (cofIsProp φ u u) a ≡ a
  prfIr {a} = cong (λ p → subst A p a) (uip (cofIsProp φ u u) refl)

  iso : A u ≅ Glue φ A B w
  iso .to a = includeA φ w u a
  iso .from (glue a _ _) = a u
  iso .inv₁ = funext (λ a → prfIr)
  iso .inv₂ = funext fg≡id where
    parEq : {a a' : (u : [ φ ]) → A u} → a u ≡ a' u → (∀ u' → a u' ≡ a' u')
    parEq {a} {a'} eq u' = subst (λ u' → a u' ≡ a' u') (cofIsProp φ u u') eq

    fg≡id : (gl : Glue φ A B w) → (includeA φ w u (gl .dom u)) ≡ gl
    fg≡id gl = glueExt (parEq prfIr) (gl .match u)

SGlue : ∀ {ℓ}
  (φ : CofProp)
  (A : [ φ ] → Set ℓ)
  (B : Set ℓ)
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  Set ℓ
SGlue φ A B f = strictify φ A (Glue φ A B f) (includeAIso φ f)

strictifyGlueIso : ∀ {ℓ}
  (φ : CofProp)
  {A : [ φ ] → Set ℓ}
  {B : Set ℓ}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  SGlue φ A B f ≅ Glue φ A B f
strictifyGlueIso φ {A} {B} f = isoB φ A (Glue φ A B f) (includeAIso φ f)

sglue : ∀ {ℓ}
  {φ : CofProp}
  {A : [ φ ] → Set ℓ}
  {B : Set ℓ}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  (u : [ φ ]) → A u → SGlue φ A B f
sglue {φ = φ} f u = strictifyGlueIso φ f .from ∘ includeA φ f u

sunglue : ∀ {ℓ}
  {φ : CofProp}
  {A : [ φ ] → Set ℓ}
  {B : Set ℓ}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  SGlue φ A B f → B
sunglue {φ = φ} f = cod ∘ strictifyGlueIso φ f .to

SGlueStrictness : ∀ {ℓ}
  (φ : CofProp)
  {A : [ φ ] → Set ℓ}
  {B : Set ℓ}
  (f : (u : [ φ ]) → A u → B)
  (u : [ φ ])
  → ---------------
  A u ≡ SGlue φ A B f
SGlueStrictness φ {A} {B} f u =
  restrictsToA φ A (Glue φ A B f) (includeAIso φ f) u

sunglue-boundary : ∀ {ℓ}
  (φ : CofProp)
  {A : [ φ ] → Set ℓ}
  {B : Set ℓ}
  (f : (u : [ φ ]) → A u → B)
  (u : [ φ ]) (a : A u)
  → sunglue f (coe (SGlueStrictness φ f u) a) ≡ f u a
sunglue-boundary φ {A} {B} f u a =
  symm
    (appdep
      (restrictsToA φ A (Glue φ A B f) (includeAIso φ f) u)
      (trans
        (congdep (λ p → cod ∘ p .snd .to) (restrictsToM φ A (Glue φ A B f) (includeAIso φ f) u))
        (symm
          (substCongAssoc (λ D → D → B) fst
            (restrictsToM φ A (Glue φ A B f) (includeAIso φ f) u) _)))
      refl)
  where
  appdep : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : Set ℓ''}
    {a a' : A} (p : a ≡ a') {f : B a → C} {f' : B a' → C}
    (q : subst (λ a → B a → C) p f ≡ f')
    {b : B a} {b' : B a'} (r : subst B p b ≡ b')
    → f b ≡ f' b'
  appdep refl refl refl = refl

----------------------------------------------------------------------
-- Indexed versions
----------------------------------------------------------------------

SGlue' : ∀ {ℓ ℓ'}
  {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (A : res Γ Φ → Set ℓ')
  (B : Γ → Set ℓ')
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  → ---------------
  Γ → Set ℓ'
SGlue' Φ A B f x = SGlue (Φ x) (λ u → A (x , u)) (B x) (λ u → f (x , u))

strictifyGlueIso' : ∀{ℓ ℓ'}
  {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  {A : res Γ Φ → Set ℓ'}
  {B : Γ → Set ℓ'}
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  → ---------------
  SGlue' Φ A B f ≅' Glue' Φ A B f
strictifyGlueIso' Φ {A} {B} f x = strictifyGlueIso (Φ x) (λ u → f (x , u))

SGlueStrictness' : ∀ {ℓ ℓ'}
  {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  {A : res Γ Φ → Set ℓ'}
  {B : Γ → Set ℓ'}
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  → ---------------
  A ≡ SGlue' Φ A B f ∘ fst
SGlueStrictness' Φ {A} {B} f =
  funext λ {(x , u) → SGlueStrictness (Φ x) (λ u' → f (x , u')) u}

module Misaligned where

  abstract

    FibSGlue : ∀ {ℓ ℓ'}
      {Γ : Set ℓ}
      (Φ : Γ → CofProp)
      {A : res Γ Φ → Set ℓ'}
      {B : Γ → Set ℓ'}
      (fe : Π (Equiv' A (B ∘ fst)))
      → ---------------
      isFib A → isFib B → isFib (SGlue' Φ A B (equivFun fe))
    FibSGlue {a} {Γ} Φ {A} {B} fe α β =
      FibIso
        (SGlue' Φ A B (equivFun fe))
        (Glue' Φ A B (equivFun fe))
        (strictifyGlueIso' Φ (equivFun fe))
        (FibGlue Φ fe α β)

    reindexSGlue : ∀ {ℓ ℓ' ℓ''}
      {Δ : Set ℓ} {Γ : Set ℓ'}
      (Φ : Γ → CofProp)
      {A : res Γ Φ → Set ℓ''}
      {B : Γ → Set ℓ''}
      (fe : Π (Equiv' A (B ∘ fst)))
      (α : isFib A) (β : isFib B)
      (ρ : Δ → Γ)
      → reindex (SGlue' Φ A B (equivFun fe)) (FibSGlue Φ fe α β) ρ
        ≡ FibSGlue (Φ ∘ ρ) (fe ∘ (ρ ×id)) (reindex A α (ρ ×id)) (reindex B β ρ)
    reindexSGlue Φ {A} {B} fe α β ρ =
      cong
        (FibIso (SGlue' Φ A B f ∘ ρ) (Glue' Φ A B f ∘ ρ) (strictifyGlueIso' Φ f ∘ ρ))
        (reindexGlue Φ fe α β ρ)
      where
      f = equivFun fe
