{-

Tinyness of shapes.

-}
module tiny where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration
open import axiom.tiny

infixr 5 _√ᴰ_

module Tiny (@♭ S : Shape) where

  open √Axioms S public

  --↓ Naturality of right-to-left transposition in the domain.

  transposeLeft^ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
    (@♭ g : A' → S √ B) (@♭ h : A → A')
    → transposeLeft g ∘ (h `^ S) ≡ transposeLeft (g ∘ h)
  transposeLeft^ g h = cong♭ transposeLeft (transposeRight^ h (transposeLeft g))

  --↓ Functoriality of √ in the type argument.

  √` : ∀ {@♭ ℓ ℓ'}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ h : A → B) → S √ A → S √ B
  √` h = transposeRight (h ∘ transposeLeft id)

  --↓ Naturality of left-to-right transposition in the codomain.

  √TransposeRight : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ f : (⟨ S ⟩ → A) → B)
    → √` h ∘ transposeRight f ≡ transposeRight (h ∘ f)
  √TransposeRight {A = A} {B} {C = C} h f =
    sym (transposeRight^ (transposeRight f) (h ∘ transposeLeft id))
    ∙ cong♭ (λ f' → transposeRight (h ∘ f')) (transposeLeft^ id (transposeRight f))

  --↓ Naturality of right-to-left transposition in the codomain.

  √TransposeLeft : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ g : A → S √ B)
    → h ∘ transposeLeft g ≡ transposeLeft (√` h ∘ g)
  √TransposeLeft h g = cong♭ transposeLeft (sym (√TransposeRight h (transposeLeft g)))

--↓ The right adjoint induces a dependent right adjoint
--↓ TODO elaborate (including about universe level)

opaque
  _√ᴰ_ : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ Γ : Type ℓ}
    (@♭ B : Γ ^ S → Type ℓ')
    → (Γ → Type (lsuc ℓ'))
  (S √ᴰ B) γ = Σ C ∈ S √ (Type* _) , √` fst C ≡ transposeRight B γ
    where
    open Tiny S

module DependentTiny (@♭ S : Shape) where

  open Tiny S

  opaque
    unfolding _√ᴰ_

    reindex√ : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      (@♭ B : Γ' ^ S → Type ℓ'')
      (@♭ ρ : Γ → Γ')
      → ∀ γ → ((S √ᴰ B) ∘ ρ) γ ≡ (S √ᴰ (B ∘ (ρ `^ S))) γ
    reindex√ B ρ _ =
      cong
        (λ T → Σ C ∈ S √ (Type* _) , √` fst C ≡ T)
        (cong$ (sym (transposeRight^ ρ B)))

  module _ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    {@♭ B : Γ' ^ S → Type ℓ''} (@♭ ρ : Γ → Γ')
    where

    computeReindex√ : Γ ⊢ˣ (S √ᴰ B) ∘ ρ →ˣ S √ᴰ (B ∘ (ρ `^ S))
    computeReindex√ γ = coe (reindex√ B ρ γ)

    expandReindex√ : Γ ⊢ˣ S √ᴰ (B ∘ (ρ `^ S)) →ˣ (S √ᴰ B) ∘ ρ
    expandReindex√ γ = coe (sym (reindex√ B ρ γ))

    computeExpandReindex√ : (b : Γ ⊢ˣ S √ᴰ (B ∘ (ρ `^ S)))
      → appˣ computeReindex√ (appˣ expandReindex√ b) ≡ b
    computeExpandReindex√ b =
      funExt λ γ → adjustSubstEq id refl _ (reindex√ B ρ γ) refl refl

    expandComputeReindex√ : (b : Γ ⊢ˣ (S √ᴰ B) ∘ ρ)
      → appˣ expandReindex√ (appˣ computeReindex√ b) ≡ b
    expandComputeReindex√ b =
      funExt λ γ → adjustSubstEq id refl _ (sym (reindex√ B ρ γ)) refl refl

  module _ {@♭ ℓ ℓ' ℓ'' ℓ'''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} {@♭ Γ'' : Type ℓ''}
    {@♭ B : Γ'' ^ S → Type ℓ'''}
    (@♭ ρ' : Γ' → Γ'') (@♭ ρ : Γ → Γ')
    where

    computeReindex√-∘ : (b : Γ ⊢ˣ (S √ᴰ B) ∘ ρ' ∘ ρ)
      → appˣ (computeReindex√ ρ) (appˣ (computeReindex√ ρ' ∘ ρ) b)
        ≡ appˣ (computeReindex√ (ρ' ∘ ρ)) b
    computeReindex√-∘ b =
      funExt λ γ →
      adjustSubstEq id
        refl
        (reindex√ B ρ' (ρ γ))
        (reindex√ (B ∘ (ρ' `^ S)) ρ γ)
        (reindex√ B (ρ' ∘ ρ) γ)
        refl

    expandReindex√-∘ : (b : Γ ⊢ˣ S √ᴰ (B ∘ (ρ' ∘ ρ) `^ S))
      → appˣ (expandReindex√ ρ' ∘ ρ) (appˣ (expandReindex√ ρ) b)
        ≡ appˣ (expandReindex√ (ρ' ∘ ρ)) b
    expandReindex√-∘ b =
      funExt λ γ →
      adjustSubstEq id
        refl
        (sym (reindex√ (B ∘ (ρ' `^ S)) ρ γ))
        (sym (reindex√ B ρ' (ρ γ)))
        (sym (reindex√ B (ρ' ∘ ρ) γ))
        refl

  module _ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ^ S → Type ℓ'} where

    opaque
      unfolding _√ᴰ_

      shut√ : @♭ (Γ ^ S ⊢ˣ B) → (Γ ⊢ˣ S √ᴰ B)
      shut√ b γ .fst = transposeRight (B ,, b) γ
      shut√ b γ .snd = cong$ (√TransposeRight fst (B ,, b))

      unshut√ : @♭ (Γ ⊢ˣ S √ᴰ B) → (Γ ^ S ⊢ˣ B)
      unshut√ t p =
        coe
          (cong$ (√TransposeLeft fst (fst ∘ t) ∙ cong♭ transposeLeft (funExt (snd ∘ t))))
          (transposeLeft (fst ∘ t) p .snd)

      unshutShut√ : (@♭ b : Γ ^ S ⊢ˣ B) → unshut√ (shut√ b) ≡ b
      unshutShut√ b =
        funExt' $ adjustSubstEq id refl refl _ refl refl

      shutUnshut√ : (@♭ t : Γ ⊢ˣ S √ᴰ B) → shut√ (unshut√ t) ≡ t
      shutUnshut√ t =
        funExt' $ Σext (cong$ (cong♭ transposeRight (sym lemma))) uip'
        where
        lemma : transposeLeft (fst ∘ t) ≡ (B ,, unshut√ t)
        lemma = funExt' $ Σext _ refl

  open√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ▷⟨ S ⟩ ^ S → Type ℓ'}
    → @♭ (Γ ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
    → Γ ⊢ˣ B ∘ ^-η S
  open√ t = unshut√ t ∘ ^-η S

  module _ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} {@♭ B : Γ' ^ S → Type ℓ''}
    where

    opaque
      unfolding reindex√ shut√

      reindexShut√ : (@♭ b : Γ' ^ S ⊢ˣ B) (@♭ ρ : Γ → Γ')
        → appˣ (computeReindex√ ρ) (shut√ b ∘ ρ) ≡ shut√ (b ∘ (ρ `^ S))
      reindexShut√ b ρ =
        funExt λ γ →
        sym
          (substCongAssoc
            id
            (λ T → Σ C ∈ _ , √` fst C ≡ T)
            (cong$ (sym (transposeRight^ ρ B))) _)
        ∙ Σext
          (substNaturality fst (cong$ (sym (transposeRight^ ρ B)))
            ∙ substConst (cong$ (sym (transposeRight^ ρ B))) _
            ∙ cong$ (sym (transposeRight^ ρ (B ,, b))))
          uip'

    opaque
      reindexUnshut√ : (@♭ g : Γ' ⊢ˣ S √ᴰ B) (@♭ ρ : Γ → Γ')
        → unshut√ g ∘ (ρ `^ S) ≡ unshut√ (appˣ (computeReindex√ ρ) (g ∘ ρ))
      reindexUnshut√ g ρ =
        sym (unshutShut√ (unshut√ g ∘ (ρ `^ S)))
        ∙ cong♭ unshut√
          (sym (reindexShut√ (unshut√ g) ρ)
            ∙ cong (appˣ (computeReindex√ ρ)) (cong (_∘ ρ) (shutUnshut√ g)))

  reindexOpen√ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    {@♭ B : Γ' ▷⟨ S ⟩ ^ S → Type ℓ''}
    (@♭ ρ : Γ → Γ')
    (@♭ t : Γ' ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
    → open√ t ∘ ρ ≡ open√ (appˣ (computeReindex√ (ρ ×id)) (t ∘ ρ ×id))
  reindexOpen√ ρ t =
    cong (_∘ ^-η S) (reindexUnshut√ t (ρ ×id))

  opaque
    openShut√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : (Γ ▷⟨ S ⟩) ^ S → Type ℓ'}
      (@♭ b : Γ ▷⟨ S ⟩ ^ S ⊢ˣ B)
      → open√ (shut√ b) ≡ b ∘ ^-η S
    openShut√ b = cong (_∘ ^-η S) (unshutShut√ b)

    shutOpen√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ^ S → Type ℓ'}
      (@♭ t : Γ ⊢ˣ S √ᴰ B)
      → t ≡ shut√ (open√ (appˣ (computeReindex√ (^-ε S)) (t ∘ ^-ε S)))
    shutOpen√ t =
      sym (shutUnshut√ t) ∙ cong♭ shut√ (cong (_∘ ^-η S) (reindexUnshut√ t (^-ε S)))

  opaque
    √ᴰPreservesProp : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → @♭ (∀ p → isStrictProp (B p))
      → ∀ γ → isStrictProp ((S √ᴰ B) γ)
    √ᴰPreservesProp {Γ = Γ} B propB γ t t' =
      cong$ {a = γ , (t , t')} lem''
      where
      preservesPropGlobal : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
        (@♭ B : Γ ^ S → Type ℓ')
        → @♭ ((@♭ b b' : Γ ^ S ⊢ˣ B) → b ≡ b')
        → ((@♭ t t' : Γ ⊢ˣ S √ᴰ B) → t ≡ t')
      preservesPropGlobal B propB t t' =
        shutOpen√ t ∙ cong♭ shut√ (propB _ _) ∙ sym (shutOpen√ t')

      lem' :
        _≡_
          {A = Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B) ⊢ˣ S √ᴰ (B ∘ (𝒑 `^ S))}
          (appˣ (computeReindex√ 𝒑) (fstˣ 𝒒))
          (appˣ (computeReindex√ 𝒑) (sndˣ 𝒒))
      lem' =
        preservesPropGlobal
          (B ∘ (𝒑 `^ S))
          (λ b b' → funExt λ p → propB (𝒑 ∘ p) (b p) (b' p))
          (appˣ (computeReindex√ 𝒑) (fstˣ 𝒒))
          (appˣ (computeReindex√ 𝒑) (sndˣ 𝒒))

      lem'' :
        _≡_
          {A = Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B) ⊢ˣ (S √ᴰ B) ∘ 𝒑}
          (fstˣ 𝒒)
          (sndˣ 𝒒)
      lem'' =
        sym (expandComputeReindex√ 𝒑 (fstˣ 𝒒))
        ∙ cong (appˣ (expandReindex√ 𝒑)) lem'
        ∙ expandComputeReindex√ 𝒑 (sndˣ 𝒒)
