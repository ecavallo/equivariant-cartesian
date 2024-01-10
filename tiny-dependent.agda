{-

Tinyness of shapes.

-}
module tiny-dependent where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration
open import axiom.tiny
open import tiny

infixr 5 _√ᴰ_


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

    doReindex√ : Γ ⊢ˣ (S √ᴰ B) ∘ ρ →ˣ S √ᴰ (B ∘ (ρ `^ S))
    doReindex√ γ = coe (reindex√ B ρ γ)

    undoReindex√ : Γ ⊢ˣ S √ᴰ (B ∘ (ρ `^ S)) →ˣ (S √ᴰ B) ∘ ρ
    undoReindex√ γ = coe (sym (reindex√ B ρ γ))

    doUndoReindex√ : (b : Γ ⊢ˣ S √ᴰ (B ∘ (ρ `^ S)))
      → appˣ doReindex√ (appˣ undoReindex√ b) ≡ b
    doUndoReindex√ b =
      funExt λ γ → adjustSubstEq id refl _ (reindex√ B ρ γ) refl refl

    undoDoReindex√ : (b : Γ ⊢ˣ (S √ᴰ B) ∘ ρ)
      → appˣ undoReindex√ (appˣ doReindex√ b) ≡ b
    undoDoReindex√ b =
      funExt λ γ → adjustSubstEq id refl _ (sym (reindex√ B ρ γ)) refl refl

  module _ {@♭ ℓ ℓ' ℓ'' ℓ'''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} {@♭ Γ'' : Type ℓ''}
    {@♭ B : Γ'' ^ S → Type ℓ'''}
    (@♭ ρ' : Γ' → Γ'') (@♭ ρ : Γ → Γ')
    where

    doReindex√-∘ : (b : Γ ⊢ˣ (S √ᴰ B) ∘ ρ' ∘ ρ)
      → appˣ (doReindex√ ρ) (appˣ (doReindex√ ρ' ∘ ρ) b)
        ≡ appˣ (doReindex√ (ρ' ∘ ρ)) b
    doReindex√-∘ b =
      funExt λ γ →
      adjustSubstEq id
        refl
        (reindex√ B ρ' (ρ γ))
        (reindex√ (B ∘ (ρ' `^ S)) ρ γ)
        (reindex√ B (ρ' ∘ ρ) γ)
        refl

    undoReindex√-∘ : (b : Γ ⊢ˣ S √ᴰ (B ∘ (ρ' ∘ ρ) `^ S))
      → appˣ (undoReindex√ ρ' ∘ ρ) (appˣ (undoReindex√ ρ) b)
        ≡ appˣ (undoReindex√ (ρ' ∘ ρ)) b
    undoReindex√-∘ b =
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
    → Γ ⊢ˣ B ∘ ^-unit S
  open√ t = unshut√ t ∘ ^-unit S

  module _ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} {@♭ B : Γ' ^ S → Type ℓ''}
    where

    opaque
      unfolding reindex√ shut√

      reindexShut√ : (@♭ b : Γ' ^ S ⊢ˣ B) (@♭ ρ : Γ → Γ')
        → appˣ (doReindex√ ρ) (shut√ b ∘ ρ) ≡ shut√ (b ∘ (ρ `^ S))
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
        → unshut√ g ∘ (ρ `^ S) ≡ unshut√ (appˣ (doReindex√ ρ) (g ∘ ρ))
      reindexUnshut√ g ρ =
        sym (unshutShut√ (unshut√ g ∘ (ρ `^ S)))
        ∙ cong♭ unshut√
          (sym (reindexShut√ (unshut√ g) ρ)
            ∙ cong (appˣ (doReindex√ ρ)) (cong (_∘ ρ) (shutUnshut√ g)))

  reindexOpen√ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    {@♭ B : Γ' ▷⟨ S ⟩ ^ S → Type ℓ''}
    (@♭ ρ : Γ → Γ')
    (@♭ t : Γ' ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
    → open√ t ∘ ρ ≡ open√ (appˣ (doReindex√ (ρ ×id)) (t ∘ ρ ×id))
  reindexOpen√ ρ t =
    cong (_∘ ^-unit S) (reindexUnshut√ t (ρ ×id))

  opaque
    openShut√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : (Γ ▷⟨ S ⟩) ^ S → Type ℓ'}
      (@♭ b : Γ ▷⟨ S ⟩ ^ S ⊢ˣ B)
      → open√ (shut√ b) ≡ b ∘ ^-unit S
    openShut√ b = cong (_∘ ^-unit S) (unshutShut√ b)

    shutOpen√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ^ S → Type ℓ'}
      (@♭ t : Γ ⊢ˣ S √ᴰ B)
      → t ≡ shut√ (open√ (appˣ (doReindex√ (^-counit S)) (t ∘ ^-counit S)))
    shutOpen√ t =
      sym (shutUnshut√ t)
      ∙ cong♭ shut√ (cong (_∘ ^-unit S) (reindexUnshut√ t (^-counit S)))

  opaque
    √ᴰPreservesPropGlobal : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → @♭ ((@♭ b b' : Γ ^ S ⊢ˣ B) → b ≡ b')
      → ((@♭ t t' : Γ ⊢ˣ S √ᴰ B) → t ≡ t')
    √ᴰPreservesPropGlobal B propB t t' =
      shutOpen√ t ∙ cong♭ shut√ (propB _ _) ∙ sym (shutOpen√ t')

    √ᴰPreservesProp : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → @♭ (∀ p → isStrictProp (B p))
      → ∀ γ → isStrictProp ((S √ᴰ B) γ)
    √ᴰPreservesProp {Γ = Γ} B propB γ t t' =
      cong$ {a = γ , (t , t')} equateGenericPoints
      where
      equateGenericPoints : Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B) ⊢ˣ fstˣ 𝒒 ≡ sndˣ 𝒒 ⦂ (S √ᴰ B) ∘ 𝒑
      equateGenericPoints =
        sym (undoDoReindex√ 𝒑 (fstˣ 𝒒))
        ∙ cong (appˣ (undoReindex√ 𝒑))
          (√ᴰPreservesPropGlobal
            (B ∘ (𝒑 `^ S))
            (λ b b' → funExt λ p → propB (𝒑 ∘ p) (b p) (b' p))
            (appˣ (doReindex√ 𝒑) (fstˣ 𝒒))
            (appˣ (doReindex√ 𝒑) (sndˣ 𝒒)))
        ∙ undoDoReindex√ 𝒑 (sndˣ 𝒒)
