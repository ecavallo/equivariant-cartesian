{-

The right adjoint √ to exponentation by a shape extends (with a caveat) to a dependent right
adjoint (DRA) √ᴰ in the sense of

[1] Birkedal, Clouston, Mannaa, Møgelberg, Pitts, & Spitters.
    Modal dependent type theory and dependent right adjoints.
    https://doi.org/10.1017/S0960129519000197

This is convenient for defining the universe of fibrations (especially with the added
complication of the equivariance condition), as observed in passing in

[2] Licata, Orton, Pitts, & Spitters.
    Internal Universes in Models of Homotopy Type Theory.
    https://doi.org/10.4230/LIPIcs.FSCD.2018.22

The caveat concerns universe level: the definition of √ᴰ uses a universe 𝑽, and √ᴰ then
takes 𝑽-small types to types in the *next* universe. Compare the construction in §4 of
[1], where local universes are used to construct a CwF with a DRA.

In the motivating cubical set semantics, there is an direct construction of this DRA
which does not raise universe level. Namely, given a type family Γˢ.A → Γˢ we apply the
right adjoint √ and reindex along the unit Γ → √(Γˢ) to define a family Γ.√B → Γ.

Γ.√B → √(Γˢ.B)
 | ⌟     |
 ↓       ↓
 Γ ———→ √(Γˢ)

However, in our internal setting we do not know that √ preserves maps with 𝑽-small fibers.

Using the fact that exponentiation by a shape has a further left adjoint (namely product
with that shape), we formulate the elimination rule in the style of

[3] Gratzer, Cavallo, Kavvos, Guatto, & Birkedal.
    Modalities and parametric adjoints.
    https://doi.org/10.1145/3514241

-}
module tiny.dependent where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration
open import axiom.tiny
open import tiny.basic

infixr 5 _√ᴰ_


--↓ Definition of the dependent right adjoint, which takes a family B over Γ ^ S and
--↓ produces a family S √ᴰ B over Γ, with the intention that we have a natural isomorphism
--↓ between sections of Γ ^ S ⊢ B and sections of Γ ⊢ S √ᴰ B.

opaque
  _√ᴰ_ : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ Γ : Type ℓ}
    (@♭ B : Γ ^ S → Type ℓ')
    → (Γ → Type (lsuc ℓ'))
  _√ᴰ_ {ℓ' = ℓ'} S B γ =
    Σ C ∈ S √ (Type* ℓ') , √` fst C ≡ transposeRight B γ
    where
    open Tiny S

module DependentTiny (@♭ S : Shape) where

  open Tiny S

  opaque
    unfolding _√ᴰ_

    --↓ The operator √ᴰ commutes with reindexing. Unfortunately this equality is not
    --↓ definition, which leads to some bureaucratic complications later on.

    reindex√ : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      (@♭ B : Γ' ^ S → Type ℓ'')
      (@♭ ρ : Γ → Γ')
      → ∀ γ → ((S √ᴰ B) ∘ ρ) γ ≡ (S √ᴰ (B ∘ (ρ `^ S))) γ
    reindex√ B ρ _ =
      cong
        (λ T → Σ C ∈ S √ (Type* _) , √` fst C ≡ T)
        (cong$ (sym (transposeRight^ ρ B)))

  --↓ Helper functions for shifting substitutions in and out of √ᴰ; these are just
  --↓ instances of coercion along the equality proven above.

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

      --↓ Introduction rule for √ᴰ, corresponding to left-to-right transposition along the
      --↓ adjunction.

      shut√ : @♭ (Γ ^ S ⊢ˣ B) → (Γ ⊢ˣ S √ᴰ B)
      shut√ b γ .fst = transposeRight (B ,, b) γ
      shut√ b γ .snd = cong$ (√TransposeRight fst (B ,, b))

      --↓ Inverse to the introduction rule, corresopnding to right-to-left transposition.

      unshut√ : @♭ (Γ ⊢ˣ S √ᴰ B) → (Γ ^ S ⊢ˣ B)
      unshut√ t γ =
        coe
          (cong$ (√TransposeLeft fst (fst ∘ t) ∙ cong♭ transposeLeft (funExt (snd ∘ t))))
          (transposeLeft (fst ∘ t) γ .snd)

      --↓ Inverse laws.

      unshutShut√ : (@♭ b : Γ ^ S ⊢ˣ B) → unshut√ (shut√ b) ≡ b
      unshutShut√ b =
        funExt' $ adjustSubstEq id refl refl _ refl refl

      shutUnshut√ : (@♭ t : Γ ⊢ˣ S √ᴰ B) → shut√ (unshut√ t) ≡ t
      shutUnshut√ t =
        funExt' $ Σext (cong$ (cong♭ transposeRight (sym lemma))) uip'
        where
        lemma : transposeLeft (fst ∘ t) ≡ (B ,, unshut√ t)
        lemma = funExt' $ Σext _ refl

  --↓ Elimination rule for √ᴰ. We prefer this to unshut√ because it lands in an arbitrary
  --↓ context Γ and thus has better properties with respect to reindexing.

  open√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ▷⟨ S ⟩ ^ S → Type ℓ'}
    → @♭ (Γ ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
    → Γ ⊢ˣ B ∘ ^-unit S
  open√ t = unshut√ t ∘ ^-unit S

  module _ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} {@♭ B : Γ' ^ S → Type ℓ''}
    where

    opaque
      unfolding reindex√ shut√

      --↓ The introduction rule commutes with reindexing.

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

    --↓ The inverse to the introduction rule commutes with reindexing along substitutions
    --↓ of the form (ρ `^ S).

    opaque
      reindexUnshut√ : (@♭ g : Γ' ⊢ˣ S √ᴰ B) (@♭ ρ : Γ → Γ')
        → unshut√ g ∘ (ρ `^ S) ≡ unshut√ (appˣ (doReindex√ ρ) (g ∘ ρ))
      reindexUnshut√ g ρ =
        sym (unshutShut√ (unshut√ g ∘ (ρ `^ S)))
        ∙ cong♭ unshut√
          (sym (reindexShut√ (unshut√ g) ρ)
            ∙ cong (appˣ (doReindex√ ρ)) (cong (_∘ ρ) (shutUnshut√ g)))

  --↓ The elimination rule commutes with reindexing.

  reindexOpen√ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    {@♭ B : Γ' ▷⟨ S ⟩ ^ S → Type ℓ''}
    (@♭ ρ : Γ → Γ')
    (@♭ t : Γ' ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
    → open√ t ∘ ρ ≡ open√ (appˣ (doReindex√ (ρ ×id)) (t ∘ ρ ×id))
  reindexOpen√ ρ t =
    cong (_∘ ^-unit S) (reindexUnshut√ t (ρ ×id))

  opaque
    --↓ Computation (β) rule.

    openShut√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : (Γ ▷⟨ S ⟩) ^ S → Type ℓ'}
      (@♭ b : Γ ▷⟨ S ⟩ ^ S ⊢ˣ B)
      → open√ (shut√ b) ≡ b ∘ ^-unit S
    openShut√ b = cong (_∘ ^-unit S) (unshutShut√ b)

    --↓ Uniqueness (η) rule.

    shutOpen√ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ^ S → Type ℓ'}
      (@♭ t : Γ ⊢ˣ S √ᴰ B)
      → t ≡ shut√ (open√ (appˣ (doReindex√ (^-counit S)) (t ∘ ^-counit S)))
    shutOpen√ t =
      sym (shutUnshut√ t)
      ∙ cong♭ shut√ (cong (_∘ ^-unit S) (reindexUnshut√ t (^-counit S)))

  opaque
    --↓ √ᴰ preserves propositions (with respect to strict equality). First we prove that
    --↓ if the type of sections of Γ ^ S ⊢ˣ B is a proposition, then so is the type of
    --↓ sections of Γ ⊢ˣ S √ᴰ B . Then we use this to deduce that if all fibers of B are
    --↓ propositions, then so are all fibers of S √ᴰ B.

    √ᴰPreservesPropSections : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → @♭ ((@♭ b b' : Γ ^ S ⊢ˣ B) → b ≡ b')
      → ((@♭ t t' : Γ ⊢ˣ S √ᴰ B) → t ≡ t')
    √ᴰPreservesPropSections B propB t t' =
      shutOpen√ t ∙ cong♭ shut√ (propB _ _) ∙ sym (shutOpen√ t')

    √ᴰPreservesProp : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → @♭ (∀ γ → isStrictProp (B γ))
      → ∀ γ → isStrictProp ((S √ᴰ B) γ)
    √ᴰPreservesProp {Γ = Γ} B propB γ t t' =
      cong$ {a = γ , (t , t')} equateGenericPoints
      where
      equateGenericPoints : Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B) ⊢ˣ fstˣ 𝒒 ≡ sndˣ 𝒒 ⦂ (S √ᴰ B) ∘ 𝒑
      equateGenericPoints =
        sym (undoDoReindex√ 𝒑 (fstˣ 𝒒))
        ∙ cong (appˣ (undoReindex√ 𝒑))
          (√ᴰPreservesPropSections
            (B ∘ (𝒑 `^ S))
            (λ b b' → funExt λ γ' → propB (𝒑 ∘ γ') (b γ') (b' γ'))
            (appˣ (doReindex√ 𝒑) (fstˣ 𝒒))
            (appˣ (doReindex√ 𝒑) (sndˣ 𝒒)))
        ∙ undoDoReindex√ 𝒑 (sndˣ 𝒒)
