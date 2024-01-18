{-

Fibration structure on Swan identity types, assuming cofibration extensionality and that
the universe of cofibrations is closed under Σ-types (i.e., is a /dominance/).

-}
module type-former.swan-identity where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration
open import fibration.trivial
open import type-former.path
open import type-former.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

--↓ Definition of cofibration extensionality.

CofExtensionality : Type
CofExtensionality = ∀ {φ ψ} → ([ φ ] → [ ψ ]) → ([ ψ ] → [ φ ]) → φ ≡ ψ

--↓ Definition of closure of Cof under Σ-types.

record CofHasΣ : Type where
  field
    _∧_ : (φ : Cof) → ([ φ ] → Cof) → Cof
    ∧-pair : ∀ {φ ψ} → (u : [ φ ]) → [ ψ u ] → [ φ ∧ ψ ]
    ∧-fst : ∀ {φ ψ} → [ φ ∧ ψ ] → [ φ ]
    ∧-snd : ∀ {φ ψ} → (uv : [ φ ∧ ψ ]) → [ ψ (∧-fst uv) ]

module SwanIdentity (ext : CofExtensionality) (dom : CofHasΣ) where

  open CofHasΣ dom

  private
    opaque
      ⊤-∧-ext : ∀ {φ ψ} → (u : [ φ ]) → φ ∧ ψ ≡ ψ u
      ⊤-∧-ext {φ} {ψ} u =
        ext
          (subst ([_] ∘ ψ) (cofIsStrictProp' φ) ∘ ∧-snd)
          (∧-pair u)

      ⊤-∨-ext : ∀ {φ ψ} → [ φ ] → (φ ∨ ψ) ≡ ⊤
      ⊤-∨-ext u = ext _ (λ _ → ∨l u)

      ∨-⊤-ext : ∀ {φ ψ} → [ ψ ] → (φ ∨ ψ) ≡ ⊤
      ∨-⊤-ext v = ext _ (λ _ → ∨r v)

      ⊥-∨-ext : ∀ {φ ψ} → ¬ [ φ ] → (φ ∨ ψ) ≡ ψ
      ⊥-∨-ext {φ} {ψ} ¬u =
        ext
          (∨-rec (𝟘-rec ∘ ¬u) id (λ _ _ → cofIsStrictProp' ψ))
          ∨r

  Constancy : {A : Type ℓ} {a₀ a₁ : A} (p : a₀ ~ a₁) → Type ℓ
  Constancy p = Σ φ ∈ Cof , ((i : 𝕀) → [ φ ] → p .at i ≡ p .at 0)

  opaque
    ConstancyExt : {A : Type ℓ} {a₀ a₁ : A} (p : a₀ ~ a₁) {c₀ c₁ : Constancy p}
      → c₀ .fst ≡ c₁ .fst
      → c₀ ≡ c₁
    ConstancyExt _ eq = Σext eq (funExt' $ funExt' uip')

  Id : {A : Type ℓ} (a₀ a₁ : A) → Type ℓ
  Id a₀ a₁ = Σ (a₀ ~ a₁) Constancy

  opaque
    IdExt : {A : Type ℓ} {a₀ a₁ : A} {q₀ q₁ : Id a₀ a₁}
      → (∀ i → q₀ .fst .at i ≡ q₁ .fst .at i)
      → q₀ .snd .fst ≡ q₁ .snd .fst
      → q₀ ≡ q₁
    IdExt {q₀ = q₀} {q₁} eq₀ eq₁ = lemma (PathExt eq₀)
      where
      lemma : q₀ .fst ≡ q₁ .fst → q₀ ≡ q₁
      lemma refl = Σext refl (ConstancyExt (q₀ .fst) eq₁)

  Constancyˣ : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ˣ A} (p : Γ ⊢ˣ Pathˣ A a₀ a₁) → (Γ → Type ℓ)
  Constancyˣ p γ = Constancy (p γ)

  Idˣ : (A : Γ → Type ℓ) (a₀ a₁ : Γ ⊢ˣ A) → (Γ → Type ℓ)
  Idˣ A a₀ a₁ γ = Id (a₀ γ) (a₁ γ)

  opaque
    ConstancyIsTFib : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ˣ A} (p : Γ ⊢ˣ Pathˣ A a₀ a₁)
      → TFibStr (Constancyˣ p)
    ConstancyIsTFib p γ (φ , a) .out .fst = φ ∧ λ u → a u .fst
    ConstancyIsTFib p γ (φ , a) .out .snd i uv = a (∧-fst uv) .snd i (∧-snd uv)
    ConstancyIsTFib p γ (φ , a) .out≡ u = ConstancyExt (p γ) (sym (⊤-∧-ext u))

  ConstancyTFib : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ˣ A}
    → Γ ⊢ˣ Pathˣ A a₀ a₁
    → Γ ⊢ᶠTriv ℓ
  ConstancyTFib p .fst = Constancyˣ p
  ConstancyTFib p .snd = ConstancyIsTFib p

  opaque
    unfolding ConstancyIsTFib
    reindexConstancyTFib : {A : Γ → Type ℓ} {a₀ a₁ : Γ ⊢ˣ A}
      {p : Γ ⊢ˣ Pathˣ A a₀ a₁} (ρ : Δ → Γ)
      → ConstancyTFib p ∘ᵗᶠ ρ ≡ ConstancyTFib (p ∘ ρ)
    reindexConstancyTFib ρ = refl

  Idᶠ : (A : Γ ⊢ᶠType ℓ) (a₀ a₁ : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
  Idᶠ A a₀ a₁ = Σᶠ (Pathᶠ A a₀ a₁) (TFibToFib (ConstancyTFib 𝒒))

  opaque
    reindexIdᶠ : {A : Γ ⊢ᶠType ℓ} {a₀ a₁ : Γ ⊢ᶠ A}
      (ρ : Δ → Γ) → Idᶠ A a₀ a₁ ∘ᶠ ρ ≡ Idᶠ (A ∘ᶠ ρ) (a₀ ∘ ρ) (a₁ ∘ ρ)
    reindexIdᶠ ρ =
      reindexΣᶠ ρ ∙
      congΣ+ Σᶠ
        (reindexPathᶠ ρ)
        (reindexTFibToFib (ρ ×id) ∙ cong TFibToFib (reindexConstancyTFib (ρ ×id)))

  idrefl : {A : Type ℓ} (a : A) → Id a a
  idrefl a .fst = refl~ a
  idrefl a .snd .fst = ⊤
  idrefl a .snd .snd _ _ = refl

  idreflᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠ Idᶠ A a a
  idreflᶠ A a γ = idrefl (a γ)

  ----------------------------------------------------------------------------------------
  -- Singleton and singleton contractibility for identity types
  ----------------------------------------------------------------------------------------

  IdSingl : {A : Type ℓ} (a : A) → Type ℓ
  IdSingl a = Σ a' ∈ _ , Id a' a

  opaque
    IdSinglExt : {A : Type ℓ} {a : A}
      {c c' : IdSingl a}
      → (∀ i → c .snd .fst .at i ≡ c' .snd .fst .at i)
      → c .snd .snd .fst ≡ c' .snd .snd .fst
      → c ≡ c'
    IdSinglExt {c = c} {c' = c'} pathEq cofEq =
      lemma (sym (c .snd .fst .at0) ∙ pathEq 0 ∙ c' .snd .fst .at0)
      where
      lemma : c .fst ≡ c' .fst → c ≡ c'
      lemma refl = Σext refl (IdExt pathEq cofEq)


  IdSinglᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
  IdSinglᶠ A a = Σᶠ A (Idᶠ (A ∘ᶠ 𝒑) 𝒒 (a ∘ 𝒑))

  idSinglCenterᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
    → Γ ⊢ᶠ IdSinglᶠ A a
  idSinglCenterᶠ A a = a ,ˣ idreflᶠ A a

  idSinglContractᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) (c : Γ ⊢ᶠ IdSinglᶠ A a)
    → Γ ⊢ᶠ Idᶠ (IdSinglᶠ A a) (idSinglCenterᶠ A a) c
  idSinglContractᶠ A a c γ = identity
    where
    box : (i : 𝕀) → OpenBox 𝕚 (cst (A $ᶠ γ)) 1
    box i .cof = ∂ i ∨ c γ .snd .snd .fst
    box i .tube j =
      ∨-rec
        (∂-rec i
          (λ _ → a γ)
          (λ _ → c γ .snd .fst .at j))
        (λ _ → a γ)
        (∂-elim i
          (λ _ v → refl)
          (λ _ v →
            c γ .snd .snd .snd j v
            ∙ sym (c γ .snd .snd .snd 1 v)
            ∙ c γ .snd .fst .at1))
    box i .cap .out = a γ
    box i .cap .out≡ =
      ∨-elimEq
        (∂-elim i (λ _ → refl) (λ _ → c γ .snd .fst .at1))
        (λ _ → refl)

    opaque
      square : (i : 𝕀) → Filler (box i)
      square i = A .snd .lift 𝕚 (cst _) 1 (box i)

    homotopy : (a γ , idrefl (a γ)) ~ c γ
    homotopy .at i .fst = square i .fill 0 .out
    homotopy .at i .snd .fst .at j = square i .fill j .out
    homotopy .at i .snd .fst .at0 = refl
    homotopy .at i .snd .fst .at1 = square i .cap≡
    homotopy .at i .snd .snd .fst = (𝕚 ∋ i ≈ 0) ∨ c γ .snd .snd .fst
    homotopy .at i .snd .snd .snd j =
      ∨-elimEq
        (λ i≡0 →
          sym (square i .fill j .out≡ (∨l (∨l i≡0)))
          ∙ square i .fill 0 .out≡ (∨l (∨l i≡0)))
        (λ v →
          sym (square i .fill j .out≡ (∨r v))
          ∙ square i .fill 0 .out≡ (∨r v))
    homotopy .at0 =
      IdSinglExt
        (λ j → sym (square 0 .fill j .out≡ (∨l (∨l refl))))
        (⊤-∨-ext refl)
    homotopy .at1 =
      IdSinglExt
        (λ j → sym (square 1 .fill j .out≡ (∨l (∨r refl))))
        (⊥-∨-ext (0≠1 ∘ sym))

    identity : Id (a γ , idrefl (a γ)) (c γ)
    identity .fst = homotopy
    identity .snd .fst = c γ .snd .snd .fst
    identity .snd .snd i v =
      IdSinglExt
        (λ j → sym (square i .fill j .out≡ (∨r v)) ∙ square 0 .fill j .out≡ (∨r v))
        (∨-⊤-ext v ∙ sym (∨-⊤-ext v))

  idSinglContrRefl : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
    → idSinglContractᶠ A a (idSinglCenterᶠ A a)
      ≡ idreflᶠ (IdSinglᶠ A a) (idSinglCenterᶠ A a)
  idSinglContrRefl A a =
    funExt λ γ →
    IdExt
      (λ i →
        idSinglContractᶠ A a (idSinglCenterᶠ A a) γ .snd .snd i tt
        ∙ idSinglContractᶠ A a (idSinglCenterᶠ A a) γ .fst .at0)
      refl

  ----------------------------------------------------------------------------------------
  -- Transport along identities
  ----------------------------------------------------------------------------------------

  module _ (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ') {a : Γ ⊢ᶠ A} (b : Γ ⊢ᶠ B ∘ᶠ (id ,, a))
    where

    idSubstᶠ : {a' : Γ ⊢ᶠ A} (p : Γ ⊢ᶠ Idᶠ A a a')
      → Γ ⊢ᶠ B ∘ᶠ (id ,, a')
    idSubstᶠ p γ =
      subst (∣ B ∣ ∘ (γ ,_)) (p γ .fst .at1)
        (B .snd .lift 𝕚 _ 0 (box p γ) .fill 1 .out)
      where
      box : {a' : Γ ⊢ᶠ A} (p : Γ ⊢ᶠ Idᶠ A a a')
        → ∀ γ → OpenBox 𝕚 (∣ B ∣ ∘ (cst γ ,, p γ .fst .at)) 0
      box p γ .cof = p γ .snd .fst
      box p γ .tube i u =
        subst
          (∣ B ∣ ∘ (γ ,_))
          (sym (p γ .snd .snd i u ∙ p γ .fst .at0))
          (b γ)
      box p γ .cap .out = subst (∣ B ∣ ∘ (γ ,_)) (sym (p γ .fst .at0)) (b γ)
      box p γ .cap .out≡ u =
        adjustSubstEq
          (∣ B ∣ ∘ (γ ,_))
          refl
          refl
          (sym (p γ .snd .snd 0 u ∙ p γ .fst .at0))
          (sym (p γ .fst .at0))
          refl

    idSubstRefl : idSubstᶠ (idreflᶠ A a) ≡ b
    idSubstRefl =
      funExt λ γ →
      sym (B .snd .lift 𝕚 _ 0 _ .fill 1 .out≡ tt)

  ----------------------------------------------------------------------------------------
  -- Paulin-Mohring style J eliminator
  ----------------------------------------------------------------------------------------

  idJᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
    (P : Γ ▷ᶠ IdSinglᶠ A a ⊢ᶠType ℓ')
    (d : Γ ⊢ᶠ P ∘ᶠ (id ,, idSinglCenterᶠ A a))
    (c : Γ ⊢ᶠ IdSinglᶠ A a)
    → Γ ⊢ᶠ P ∘ᶠ (id ,, c)
  idJᶠ A a P d c =
    idSubstᶠ (IdSinglᶠ A a) P d (idSinglContractᶠ A a c)

  idJreflᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
    (P : Γ ▷ᶠ IdSinglᶠ A a ⊢ᶠType ℓ')
    (d : Γ ⊢ᶠ P ∘ᶠ (id ,, idSinglCenterᶠ A a))
    → idJᶠ A a P d (idSinglCenterᶠ A a) ≡ d
  idJreflᶠ A a P d =
    cong (idSubstᶠ (IdSinglᶠ A a) P d) (idSinglContrRefl A a)
    ∙ idSubstRefl (IdSinglᶠ A a) P d
