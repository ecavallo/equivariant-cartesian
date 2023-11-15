{-

Strict Glue types and their (unaligned) fibrancy.

-}
{-# OPTIONS --rewriting #-}
module glueing.strict where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.equivs
open import type-formers.pi

open import glueing.weak

private variable ℓ ℓ' ℓ'' : Level

----------------------------------------------------------------------
-- Strict glueing
----------------------------------------------------------------------

opaque
  includeA : (φ : CofProp)
    {A : [ φ ] → Set ℓ}
    {B : Set ℓ}
    (f : (u : [ φ ]) → A u → B)
    → ---------------
    (u : [ φ ]) → A u → Glue φ A B f
  includeA φ {A} {B} f u a .dom v = subst A (cofIsProp φ _ _) a
  includeA φ {A} {B} f u a .cod = f u a
  includeA φ {A} {B} f u a .match v =
    cong (uncurry f) (sym (Σext (cofIsProp φ _ _) refl))

  includeAIso : (φ : CofProp)
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
    iso .inv₂ = funext fg≡id
      where
      parEq : {a a' : (u : [ φ ]) → A u} → a u ≡ a' u → (∀ u' → a u' ≡ a' u')
      parEq {a} {a'} eq u' = subst (λ u' → a u' ≡ a' u') (cofIsProp φ u u') eq

      fg≡id : (gl : Glue φ A B w) → (includeA φ w u (gl .dom u)) ≡ gl
      fg≡id gl = GlueExt (parEq prfIr) (gl .match u)

  SGlue : (φ : CofProp)
    (A : [ φ ] → Set ℓ)
    (B : Set ℓ)
    (f : (u : [ φ ]) → A u → B)
    → ---------------
    Set ℓ
  SGlue φ A B f = realign φ A (Glue φ A B f) (includeAIso φ f)

  strictifyGlueIso : (φ : CofProp)
    {A : [ φ ] → Set ℓ}
    {B : Set ℓ}
    (f : (u : [ φ ]) → A u → B)
    → ---------------
    SGlue φ A B f ≅ Glue φ A B f
  strictifyGlueIso φ {A} {B} f = isoB φ A (Glue φ A B f) (includeAIso φ f)

  sglue : {φ : CofProp}
    {A : [ φ ] → Set ℓ}
    {B : Set ℓ}
    (f : (u : [ φ ]) → A u → B)
    → ---------------
    (u : [ φ ]) → A u → SGlue φ A B f
  sglue {φ = φ} f u = strictifyGlueIso φ f .from ∘ includeA φ f u

  sunglue : {φ : CofProp}
    {A : [ φ ] → Set ℓ}
    {B : Set ℓ}
    (f : (u : [ φ ]) → A u → B)
    → ---------------
    SGlue φ A B f → B
  sunglue {φ = φ} f = cod ∘ strictifyGlueIso φ f .to

  SGlueStrictness : (φ : CofProp)
    {A : [ φ ] → Set ℓ}
    {B : Set ℓ}
    (f : (u : [ φ ]) → A u → B)
    (u : [ φ ])
    → ---------------
    A u ≡ SGlue φ A B f
  SGlueStrictness φ {A} {B} f u =
    restrictsToA φ A (Glue φ A B f) (includeAIso φ f) u

  sunglue-boundary : (φ : CofProp)
    {A : [ φ ] → Set ℓ}
    {B : Set ℓ}
    (f : (u : [ φ ]) → A u → B)
    (u : [ φ ]) (a : A u)
    → sunglue f (coe (SGlueStrictness φ f u) a) ≡ f u a
  sunglue-boundary φ {A} {B} f u a =
    sym
      (appdep
        (restrictsToA φ A (Glue φ A B f) (includeAIso φ f) u)
        (sym
          (substCongAssoc (λ D → D → B) fst
            (restrictsToM φ A (Glue φ A B f) (includeAIso φ f) u) _)
         ∙
         congdep (λ p → cod ∘ p .snd .to) (restrictsToM φ A (Glue φ A B f) (includeAIso φ f) u))
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

SGlueᴵ : {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  (A : Γ ,[ Φ ] → Set ℓ')
  (B : Γ → Set ℓ')
  (f : Γ ,[ Φ ] ⊢ A →ᴵ (B ∘ fst))
  → ---------------
  Γ → Set ℓ'
SGlueᴵ Φ A B f x = SGlue (Φ x) (A ∘ (x ,_)) (B x) (f ∘ (x ,_))

strictifyGlueIsoᴵ : {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  {A : Γ ,[ Φ ] → Set ℓ'}
  {B : Γ → Set ℓ'}
  (f : Γ ,[ Φ ] ⊢ A →ᴵ (B ∘ fst))
  → ---------------
  SGlueᴵ Φ A B f ≅ᴵ Glueᴵ Φ A B f
strictifyGlueIsoᴵ Φ f x = strictifyGlueIso (Φ x) (f ∘ (x ,_))

SGlueStrictnessᴵ : {Γ : Set ℓ}
  (Φ : Γ → CofProp)
  {A : Γ ,[ Φ ] → Set ℓ'}
  {B : Γ → Set ℓ'}
  (f : Γ ,[ Φ ] ⊢ A →ᴵ (B ∘ fst))
  → ---------------
  A ≡ SGlueᴵ Φ A B f ∘ fst
SGlueStrictnessᴵ Φ f =
  funext λ (x , u) → SGlueStrictness (Φ x) (f ∘ (x ,_)) u

module Misaligned where

  GlueIsFib→SGlueIsFib : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ A (B ∘ fst))
    → ---------------
    isFib (Glueᴵ Φ A B (equivFun fe)) → isFib (SGlueᴵ Φ A B (equivFun fe))
  GlueIsFib→SGlueIsFib Φ {A} {B} fe γ =
    isomorphIsFib
      (strictifyGlueIsoᴵ Φ (equivFun fe))
      γ

  SGlueIsFib : {Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ'}
    {B : Γ → Set ℓ'}
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ A (B ∘ fst))
    → ---------------
    isFib A → isFib B → isFib (SGlueᴵ Φ A B (equivFun fe))
  SGlueIsFib Φ {A} {B} fe α β =
    isomorphIsFib
      (strictifyGlueIsoᴵ Φ (equivFun fe))
      (GlueIsFib Φ fe α β)

  reindexSGlue : {Δ : Set ℓ} {Γ : Set ℓ'}
    (Φ : Γ → CofProp)
    {A : Γ ,[ Φ ] → Set ℓ''}
    {B : Γ → Set ℓ''}
    (fe : Γ ,[ Φ ] ⊢ Equivᴵ A (B ∘ fst))
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (SGlueIsFib Φ fe α β) ρ
      ≡ SGlueIsFib (Φ ∘ ρ) (fe ∘ (ρ ×id)) (reindex α (ρ ×id)) (reindex β ρ)
  reindexSGlue Φ {A} {B} fe α β ρ =
    reindexIsomorph (strictifyGlueIsoᴵ Φ (equivFun fe)) _ ρ
    ∙ cong (GlueIsFib→SGlueIsFib (Φ ∘ ρ) (fe ∘ ρ ×id)) (reindexGlue Φ fe α β ρ)
