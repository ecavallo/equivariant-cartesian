{-

Fibrancy of the universe

TODO discuss non-use of fibration.extension

-}
module universe.fibrant where

open import prelude
open import axioms
open import cofibration
open import fibration.fibration
open import type-formers.equivs
open import type-formers.glue
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma
open import universe.core

private variable
  ℓ : Level
  Γ : Type ℓ

module _ {@♭ ℓ} where

  ----------------------------------------------------------------------------------------
  -- The universe is closed under Glue-types
  ----------------------------------------------------------------------------------------

  universalGlueCtx : Type (lsuc ℓ)
  universalGlueCtx =
    Cof
    ▷ 𝑼ᴵ ℓ
    ▷ (λ (φ , _) → [ φ ] → 𝑼 ℓ)
    ▷ (λ (φ , B , A) → (u : [ φ ]) → Equiv (El (A u)) (El B))

  universalGlueᶠ : universalGlueCtx ⊢ᶠType ℓ
  universalGlueᶠ =
    Glueᶠ
      (λ (φ , _ , _ , _) → φ)
      (Elᶠ λ (_ , B , _ , _) → B)
      (Elᶠ λ (_ , _ , A , _ , u) → A u)
      (λ (_ , _ , _ , fe , u) → fe u)

  glue : (φ : Cof) (b : 𝑼 ℓ) (a : [ φ ] → 𝑼 ℓ)
    (fe : (u : [ φ ]) → Equiv (El (a u)) (El b))
    → 𝑼 ℓ
  glue φ b a fe = encode universalGlueᶠ (φ , b , a , fe)

  glueMatch : (φ : Cof) (b : 𝑼 ℓ) (a : [ φ ] → 𝑼 ℓ)
    (fe : (u : [ φ ]) → Equiv (El (a u)) (El b))
    (u : [ φ ]) → a u ≡ glue φ b a fe
  glueMatch φ b a fe u =
    appCong (sym (encodeDecode (λ (_ , _ , A , _ , u) → A u)))
    ∙ appCong (cong♭ encode (GlueᶠMatch _ _ _ _))
    ∙ encodeReindexFib universalGlueᶠ fst (_ , u)

  Glueᵁ : (φ : Γ → Cof) (b : Γ ⊢ 𝑼ᴵ ℓ) (a : Γ ▷[ φ ] ⊢ 𝑼ᴵ ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ (Elᶠ a) (Elᶠ (b ∘ fst)))
    → Γ ⊢ 𝑼ᴵ ℓ
  Glueᵁ φ b a fe γ =
    glue (φ γ) (b γ) (a ∘ (γ ,_)) (fe ∘ (γ ,_))

  decodeGlue : (φ : Γ → Cof) (b : Γ ⊢ 𝑼ᴵ ℓ) (a : Γ ▷[ φ ] ⊢ 𝑼ᴵ ℓ)
    (fe : Γ ▷[ φ ] ⊢ᶠ Equivᶠ (Elᶠ a) (Elᶠ (b ∘ fst)))
    → decode (Glueᵁ φ b a fe) ≡ Glueᶠ φ (decode b) (decode a) fe
  decodeGlue φ b a fe =
    cong (_∘ᶠ (φ ,, b ,, curry a ,, curry fe)) (decodeEncode universalGlueᶠ)
    ∙ reindexGlueᶠ (φ ,, b ,, curry a ,, curry fe)

  ----------------------------------------------------------------------------------------
  -- Fibrancy of the universe
  ----------------------------------------------------------------------------------------

  module 𝑼Lift {S r} (box : OpenBox S r (𝑼ᴵ ℓ)) where

    partialEquiv : ∀ s
      → [ box .cof ∨ S ∋ r ≈ s ]
      → Σ a ∈ 𝑼 ℓ , Equiv (El a) (El (box .cap .out))
    partialEquiv s =
      ∨-rec (box .cof) (S ∋ r ≈ s)
        (λ u →
          box .tube s u ,
          subst (Equiv _ ∘ El) (box .cap .out≡ u) (coerceEquiv S (Elᶠ (box .tube ⦅–⦆ u)) s r))
        (λ _ → box .cap .out , idEquivᶠ (Elᶠ id) (box .cap .out))
        (λ {u refl →
          Σext
            (box .cap .out≡ u)
            (eqLemma (box .cap .out≡ u) (coerceEquivCap S (Elᶠ (box .tube ⦅–⦆ u)) r))})
      where
      eqLemma : {A B : 𝑼 ℓ} (eq : A ≡ B) {e : Equiv (El A) (El A)}
        → e ≡ idEquivᶠ (Elᶠ id) A
        → subst ((Equiv ⦅–⦆ _) ∘ El) eq (subst (Equiv _ ∘ El) eq e) ≡ idEquivᶠ (Elᶠ id) B
      eqLemma refl eq = eq

    filler : Filler box
    filler .fill s .out =
      glue (box .cof ∨ S ∋ r ≈ s) (box .cap .out)
        (λ u → partialEquiv s u .fst)
        (λ u → partialEquiv s u .snd)
    filler .fill s .out≡ u = glueMatch _ _ _ _ (∨l u)
    filler .cap≡ = sym (glueMatch _ _ _ _ (∨r refl))

  opaque
    𝑼FibStr : FibStr {Γ = 𝟙} (𝑼ᴵ ℓ)
    𝑼FibStr .lift S r p box = 𝑼Lift.filler box
    𝑼FibStr .vary S T σ r p box s =
      congΣ ((encode universalGlueᶠ ∘_) ∘ unpack) cofEq $
      substDom [_] cofEq _ ∙ (funExt λ uv → partialEquivEq (subst [_] (sym cofEq) uv) uv)
      where
      unpack : (φ : Cof)
        → ([ φ ] → Σ a ∈ 𝑼 ℓ , Equiv (El a) (El (box .cap .out)))
        → universalGlueCtx
      unpack φ afe = φ , box .cap .out , fst ∘ afe , snd ∘ afe

      cofEq : (box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (box .cof ∨ S ∋ r ≈ s)
      cofEq = cong (box .cof ∨_) (≈Equivariant σ r s)

      partialEquivEq : ∀ uv uv'
        → 𝑼Lift.partialEquiv box (⟪ σ ⟫ s) uv ≡ 𝑼Lift.partialEquiv (reshapeBox σ box) s uv'
      partialEquivEq uv =
        ∨-elimEq (box .cof) (S ∋ r ≈ s)
          (λ u →
            cong (𝑼Lift.partialEquiv box (⟪ σ ⟫ s)) (trunc uv (∨l u))
            ∙ Σext refl
              (cong (subst (Equiv _ ∘ El) (box .cap .out≡ u))
                (coerceEquivVary σ (Elᶠ (box .tube ⦅–⦆ u)) s r)))
          (λ {refl → cong (𝑼Lift.partialEquiv box (⟪ σ ⟫ s)) (trunc uv (∨r refl))})

𝑼ᶠ : ∀ (@♭ ℓ) → Γ ⊢ᶠType (lsuc ℓ )
𝑼ᶠ ℓ .fst = 𝑼ᴵ ℓ
𝑼ᶠ ℓ .snd = 𝑼FibStr ∘ᶠˢ cst tt
