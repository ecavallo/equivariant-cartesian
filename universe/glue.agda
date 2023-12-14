{-

Closure of the universe under Glue types.
This is later used to prove that the universe is fibrant.

-}
module universe.glue where

open import prelude
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration
open import type-former.equiv
open import type-former.glue
open import type-former.path
open import type-former.pi
open import type-former.sigma
open import universe.core

private variable
  ℓ : Level
  Γ : Type ℓ

----------------------------------------------------------------------------------------
-- The universe is closed under Glue-types
----------------------------------------------------------------------------------------

module _ {@♭ ℓ} where

  private
    universalGlueCtx : Type (lsuc ℓ)
    universalGlueCtx =
      Cof
      ▷ˣ 𝑼ˣ ℓ
      ▷ˣ (λ (φ , _) → [ φ ] → 𝑼 ℓ)
      ▷ˣ (λ (φ , B , A) → (u : [ φ ]) → El (A u) ≃ El B)

    universalGlueᶠ : universalGlueCtx ⊢ᶠType ℓ
    universalGlueᶠ =
      Glueᶠ
        (λ (φ , _ , _ , _) → φ)
        (Elᶠ λ (_ , B , _ , _) → B)
        (Elᶠ λ (_ , _ , A , _ , u) → A u)
        (λ (_ , _ , _ , fe , u) → fe u)

  Glueᵁ : (φ : Cof) (B : 𝑼 ℓ) (A : [ φ ] → 𝑼 ℓ)
    (fe : (u : [ φ ]) → El (A u) ≃ El B)
    → 𝑼 ℓ
  Glueᵁ φ B A fe = encode universalGlueᶠ (φ , B , A , fe)

  opaque
    GlueᵁMatch : (φ : Cof) (B : 𝑼 ℓ) (A : [ φ ] → 𝑼 ℓ)
      (fe : (u : [ φ ]) → El (A u) ≃ El B)
      (u : [ φ ]) → A u ≡ Glueᵁ φ B A fe
    GlueᵁMatch φ b a fe u =
      appCong (sym (encodeDecode (λ (_ , _ , A , _ , u) → A u)))
      ∙ appCong (cong♭ encode (GlueᶠMatch _ _ _ _))
      ∙ encodeReindexFib universalGlueᶠ fst (_ , u)

  Glueᵁᶠ : (φ : Γ → Cof) (b : Γ ⊢ˣ 𝑼ˣ ℓ) (a : Γ ▷[ φ ] ⊢ˣ 𝑼ˣ ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Elᶠ a ≃ᶠ Elᶠ (b ∘ fst))
    → Γ ⊢ˣ 𝑼ˣ ℓ
  Glueᵁᶠ φ b a fe γ =
    Glueᵁ (φ γ) (b γ) (a ∘ (γ ,_)) (fe ∘ (γ ,_))

  opaque
    decodeGlue : (φ : Γ → Cof) (b : Γ ⊢ˣ 𝑼ˣ ℓ) (a : Γ ▷[ φ ] ⊢ˣ 𝑼ˣ ℓ)
      (fe : Γ ▷[ φ ] ⊢ᶠ Elᶠ a ≃ᶠ Elᶠ (b ∘ fst))
      → decode (Glueᵁᶠ φ b a fe) ≡ Glueᶠ φ (decode b) (decode a) fe
    decodeGlue φ b a fe =
      cong (_∘ᶠ (φ ,, b ,, curry a ,, curry fe)) (decodeEncode universalGlueᶠ)
      ∙ reindexGlueᶠ (φ ,, b ,, curry a ,, curry fe)

  unglueᵁ : {φ : Cof} {B : 𝑼 ℓ} {A : [ φ ] → 𝑼 ℓ}
    {fe : (u : [ φ ]) → El (A u) ≃ El B}
    → El (Glueᵁ φ B A fe) → El B
  unglueᵁ {B = B} =
    subst
      (λ C → C → El B)
      (appCong $ cong fst $ sym $ decodeGlue _ _ _ _)
      (unglueᶠ _ _ _ _ tt)

  unglueᵁEquiv : {φ : Cof} {B : 𝑼 ℓ} {A : [ φ ] → 𝑼 ℓ}
    {fe : (u : [ φ ]) → El (A u) ≃ El B}
    → El (Glueᵁ φ B A fe) ≃ El B
  unglueᵁEquiv .fst = unglueᵁ
  unglueᵁEquiv .snd =
    subst
      (λ (C , f) → IsEquiv {A = C} f)
      (Σext (appCong $ cong fst $ sym $ decodeGlue _ _ _ _) refl)
      (unglueᶠIsEquiv _ _ _ _ tt)

  opaque
    unglueᵁMatch : {φ : Cof} {B : 𝑼 ℓ} {A : [ φ ] → 𝑼 ℓ}
      {fe : (u : [ φ ]) → El (A u) ≃ El B}
      (u : [ φ ])
      → subst (λ C → El C → El B) (GlueᵁMatch φ B A fe u) (fe u .fst) ≡ unglueᵁ
    unglueᵁMatch {B = B} u =
      substCongAssoc (λ C → C → El B) El (GlueᵁMatch _ _ _ _ u) _
      ∙ adjustSubstEq (λ C → C → El B)
          (cong (_$ᶠ (tt , u)) $ GlueᶠMatch _ _ _ _)
          refl
          (cong El (GlueᵁMatch _ _ _ _ u))
          (appCong $ cong fst $ sym $ decodeGlue _ _ _ _)
          (sym $ substCongAssoc
            (λ C → C → El B)
            (λ C → C $ᶠ (tt , u))
            (GlueᶠMatch _ _ _ _) _)
      ∙ cong (subst (λ C → C → El B) (appCong $ cong fst $ sym $ decodeGlue _ _ _ _))
          (congdep₂ (λ _ → _$ (tt , u)) (GlueᶠMatch _ _ _ _) (unglueᶠMatch _ _ _ _))
