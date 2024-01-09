{-

Constructing a universe that classifies fibrations

-}
module universe.core where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import tiny
open import fibration.fibration
open import type-former.sigma

private variable
  ℓ ℓ' : Level
  Γ : Type ℓ

open DependentTiny

opaque
  hasLifts : (S : Shape) (A : ⟨ S ⟩ → Type ℓ) → Type ℓ
  hasLifts S A = ∀ r (box : OpenBox S r A) → Filler box

hasLiftsˣ : (S : Shape)
  (A : Γ ▷⟨ S ⟩ → Type ℓ)
  → (Γ → Type ℓ)
hasLiftsˣ S A γ = hasLifts S (A ∘ (γ ,_))

𝑼Lifts : ∀ (@♭ ℓ) → Type (lsuc ℓ)
𝑼Lifts ℓ = Σ A ∈ Type ℓ , ((@♭ S : Shape) → (S √ᴰ hasLifts S) A)

𝑼Liftsˣ : ∀ (@♭ ℓ) → (Γ → Type (lsuc ℓ))
𝑼Liftsˣ ℓ _ = 𝑼Lifts ℓ

opaque
  unfolding hasLifts
  decodeLifts : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ S : Shape)
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ˣ 𝑼Liftsˣ ℓ')
    → Γ ⊢ˣ hasLiftsˣ S (fstˣ A)
  decodeLifts S A =
    open√ S $♭
    appˣ (computeReindex√ S (fst ∘ A)) $
    λ γs → A γs .snd S

opaque
  unfolding decodeLifts
  reindexDecodeLifts : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ) (@♭ S : Shape)
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ˣ 𝑼Liftsˣ ℓ'')
    → decodeLifts S A ∘ ρ ≡ decodeLifts S (A ∘ (ρ ×id))
  reindexDecodeLifts ρ S A =
    reindexOpen√ S _ _ ∙
    cong♭ (open√ S) (computeReindex√-∘ S (fst ∘ A) (ρ ×id) _)

opaque
  unfolding hasLifts
  hasVaries : ∀ {@♭ ℓ} (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
    (A : ⟨ T ⟩ → 𝑼Lifts ℓ) → Type ℓ
  hasVaries S T σ A =
    ∀ r box s →
    decodeLifts T (^-ε T) A (⟪ σ ⟫ r) box .fill (⟪ σ ⟫ s) .out
    ≡ decodeLifts S (^-ε S) (A ∘ ⟪ σ ⟫) r (reshapeBox σ box) .fill s .out

opaque
  unfolding hasVaries
  hasVariesIsProp : ∀ {@♭ ℓ} (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
    (A : ⟨ T ⟩ → 𝑼Lifts ℓ)
    (v v' : hasVaries S T σ A) → v ≡ v'
  hasVariesIsProp S T σ A v v' =
    funExt' $ funExt' $ funExt' uip'

hasVariesˣ : ∀ {@♭ ℓ ℓ'} (@♭ S T : Shape) (@♭ σ : ShapeHom S T) {Γ : Type ℓ}
  (A : Γ ▷⟨ T ⟩ ⊢ˣ 𝑼Liftsˣ ℓ')
  → (Γ → Type ℓ')
hasVariesˣ S T σ A γ = hasVaries S T σ (A ∘ (γ ,_))

𝑼 : ∀ (@♭ ℓ) → Type (lsuc ℓ)
𝑼 ℓ = Σ A ∈ 𝑼Lifts ℓ , (∀ (@♭ S T) (@♭ σ : ShapeHom S T) → (T √ᴰ hasVaries S T σ) A)

El : ∀ {@♭ ℓ} → 𝑼 ℓ → Type ℓ
El = fst ∘ fst

𝑼ˣ : ∀ (@♭ ℓ) → (Γ → Type (lsuc ℓ))
𝑼ˣ ℓ _ = 𝑼 ℓ

decodeVaries : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
  (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
  (@♭ A : Γ ▷⟨ T ⟩ ⊢ˣ 𝑼ˣ ℓ')
  → Γ ⊢ˣ hasVariesˣ S T σ (fstˣ A)
decodeVaries S T σ A =
  open√ T $♭
  appˣ (computeReindex√ T (fst ∘ A)) $
  λ γt → A γt .snd S T σ

------------------------------------------------------------------------------------------
-- El : 𝑼 → Type is a fibration
------------------------------------------------------------------------------------------

opaque
  unfolding hasLifts hasVaries
  ElFibStr : ∀ {@♭ ℓ} → FibStr (El {ℓ})
  ElFibStr .lift =
    ShapeIsDiscrete λ (@♭ S) →
    λ r A → decodeLifts S (^-ε S) (fst ∘ A) r
  ElFibStr .vary =
    ShapeIsDiscrete λ (@♭ S) →
    ShapeIsDiscrete λ (@♭ T) →
    ShapeHomIsDiscrete λ (@♭ σ) →
    λ r A → decodeVaries S T σ (^-ε T) A r

Elˣ : ∀ {@♭ ℓ} → (Γ ⊢ˣ 𝑼ˣ ℓ) → (Γ → Type ℓ)
Elˣ = El ∘_

Elᶠ : ∀ {@♭ ℓ} → (Γ ⊢ˣ 𝑼ˣ ℓ) → Γ ⊢ᶠType ℓ
Elᶠ = (El , ElFibStr) ∘ᶠ_

decode = Elᶠ

------------------------------------------------------------------------------------------
-- Any fibration induces a map into 𝑼
------------------------------------------------------------------------------------------

opaque
  unfolding hasLifts
  getFibLifts : (S : Shape)
    (A : Γ ▷⟨ S ⟩ ⊢ᶠType ℓ)
    → Γ ⊢ˣ hasLiftsˣ S ∣ A ∣
  getFibLifts S A γ r box = A .snd .lift S r (γ ,_) box

opaque
  unfolding hasLifts
  encodeHasLifts : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → Γ ⊢ˣ (S √ᴰ hasLifts S) ∘ ∣ A ∣
  encodeHasLifts S A =
    appˣ (expandReindex√ S ∣ A ∣) $
    shut√ S $♭
    λ p r box → A .snd .lift S r p box

  reindexEncodeHasLifts : ∀ {@♭ ℓ ℓ' ℓ''} (@♭ S : Shape)
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ)
    (@♭ A : Γ ⊢ᶠType ℓ'')
    → encodeHasLifts S A ∘ ρ ≡ encodeHasLifts S (A ∘ᶠ ρ)
  reindexEncodeHasLifts S ρ A =
    cong (appˣ (expandReindex√ S ∣ A ∣ ∘ ρ))
      (sym (expandComputeReindex√ S ρ _)
        ∙ cong (appˣ (expandReindex√ S ρ)) (reindexShut√ S _ ρ))
    ∙ expandReindex√-∘ S ∣ A ∣ ρ _

encodeLifts : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} → @♭ (Γ ⊢ᶠType ℓ') → Γ ⊢ˣ 𝑼Liftsˣ ℓ'
encodeLifts A γ .fst = A $ᶠ γ
encodeLifts A γ .snd S = encodeHasLifts S A γ

opaque
  reindexEncodeLifts : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ)
    (@♭ A : Γ ⊢ᶠType ℓ'')
    → encodeLifts A ∘ ρ ≡ encodeLifts (A ∘ᶠ ρ)
  reindexEncodeLifts ρ A =
    funExt λ γ →
    Σext refl (funExt♭ λ S → cong$ (reindexEncodeHasLifts S ρ A))

opaque
  unfolding encodeHasLifts decodeLifts getFibLifts
  decodeEncodeLifts : ∀ {@♭ ℓ ℓ'} {@♭ S : Shape} {@♭ Γ : Type ℓ}
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ᶠType ℓ')
    → decodeLifts S (encodeLifts A) ≡ getFibLifts S A
  decodeEncodeLifts {S = S} A =
    cong♭ (open√ S) (computeExpandReindex√ S _ _)
    ∙ openShut√ _ _

private
  reindexEncodeInsideDecode : ∀ {@♭ ℓ ℓ' ℓ''}
    (@♭ S : Shape)
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' ▷⟨ S ⟩ → Γ)
    (@♭ A : Γ ⊢ᶠType ℓ'')
    → decodeLifts S (encodeLifts A ∘ ρ) ≡ decodeLifts S (encodeLifts (A ∘ᶠ ρ))
  reindexEncodeInsideDecode S ρ A =
    cong (subst (λ B → _ ⊢ˣ hasLiftsˣ S B) ⦅–⦆ (decodeLifts S (encodeLifts A ∘ ρ))) uip'
    ∙ sym (substCongAssoc (λ B → _ ⊢ˣ hasLiftsˣ S B) fstˣ (reindexEncodeLifts ρ A) _)
    ∙ congdep♭ (decodeLifts S) (reindexEncodeLifts ρ A)

opaque
  unfolding hasLifts getFibLifts hasVaries
  encodeHasVaries : ∀ {@♭ ℓ ℓ'}
    (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
    {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → Γ ⊢ˣ (T √ᴰ hasVaries S T σ) ∘ encodeLifts A
  encodeHasVaries S T σ A =
    appˣ (expandReindex√ T (encodeLifts A)) $
    shut√ T $♭
    λ p r box s →
    cong (λ l → l p (⟪ σ ⟫ r) box .fill (⟪ σ ⟫ s) .out)
      (reindexDecodeLifts (encodeLifts A `^ T) T (^-ε T)
        ∙ reindexEncodeInsideDecode T (^-ε T) A
        ∙ decodeEncodeLifts (A ∘ᶠ ^-ε T))
    ∙ A .snd .vary S T σ r p box s
    ∙ cong (λ l → l (p ∘ ⟪ σ ⟫) r (reshapeBox σ box) .fill s .out)
        (sym
          (reindexDecodeLifts (encodeLifts A `^ S) S (^-ε S)
            ∙ reindexEncodeInsideDecode S (^-ε S) A
            ∙ decodeEncodeLifts (A ∘ᶠ ^-ε S)))

opaque
  encode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} → @♭ (Γ ⊢ᶠType ℓ') → (Γ ⊢ˣ 𝑼ˣ ℓ')
  encode {ℓ' = ℓ'} {Γ} A = encoding
    where
    encoding : Γ ⊢ˣ 𝑼ˣ ℓ'
    encoding γ .fst = encodeLifts A γ
    encoding γ .snd S T σ = encodeHasVaries S T σ A γ

------------------------------------------------------------------------------------------
-- Inverse conditions for the correspondence between Fib Γ and Γ ⊢ˣ 𝑼ˣ
------------------------------------------------------------------------------------------

opaque
  unfolding encode ElFibStr getFibLifts
  decodeEncode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → decode (encode A) ≡ A
  decodeEncode A =
    Σext refl $
    FibStrExt {α = ElFibStr ∘ᶠˢ (encode A)} $
    ShapeIsDiscrete λ (@♭ S) r p box s →
    cong (λ lifter → lifter r box .fill s .out) (mainLemma S p)
    where
    mainLemma : ∀ (@♭ S) p →
      decodeLifts S (^-ε S) (encodeLifts A ∘ p) ≡ getFibLifts S (A ∘ᶠ ^-ε S) p
    mainLemma S p =
      cong$ (reindexDecodeLifts (encodeLifts A `^ S) S (^-ε S))
      ∙ cong$ (reindexEncodeInsideDecode S (^-ε S) A)
      ∙ cong$ (decodeEncodeLifts (A ∘ᶠ ^-ε S))

opaque
  𝑼Ext : ∀ {@♭ ℓ} {C C' : 𝑼 ℓ} → C .fst ≡ C' .fst → C ≡ C'
  𝑼Ext eq =
    Σext eq $
    funExt♭ λ S → funExt♭ λ T → funExt♭ λ σ →
    √ᴰPreservesProp' T (hasVaries S T σ) (λ _ → hasVariesIsProp S T σ _) _ _ _

opaque
  unfolding encode
  reindexEncode : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Δ : Type ℓ} {@♭ Γ : Type ℓ'}
    (@♭ A : Γ ⊢ᶠType ℓ'') (@♭ ρ : Δ → Γ)
    → encode A ∘ ρ ≡ encode (A ∘ᶠ ρ)
  reindexEncode A ρ =
    funExt' $ 𝑼Ext $ cong$ $ reindexEncodeLifts ρ A

opaque
  unfolding encode ElFibStr encodeHasLifts decodeLifts
  encodeEl : ∀ {@♭ ℓ} → (C : 𝑼 ℓ) → encode (Elᶠ id) C ≡ C
  encodeEl {ℓ = ℓ} =
    λ C → 𝑼Ext $ Σext refl (funExt♭ λ S → cong$ (lemma S))
    where
    get√Lifts : (@♭ S : Shape) (C : 𝑼 ℓ) → (S √ᴰ hasLifts S) (El C)
    get√Lifts S C = C .fst .snd S

    lemma : (@♭ S : Shape)
      → encodeHasLifts S (Elᶠ {ℓ = ℓ} id) ≡ get√Lifts S
    lemma S =
      cong (appˣ (expandReindex√ S El))
        (cong♭ (shut√ S)
          (reindexDecodeLifts (fst `^ S) S (^-ε S)
            ∙ cong♭ (open√ S)
                (sym (computeReindex√-∘ S El (^-ε S) (get√Lifts S ∘ ^-ε S))))
          ∙ sym (shutOpen√ S (appˣ (computeReindex√ S El) (get√Lifts S))))
      ∙ expandComputeReindex√ S El (get√Lifts S)

opaque
  encodeDecode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ C : Γ ⊢ˣ 𝑼ˣ ℓ') → encode (decode C) ≡ C
  encodeDecode C = funExt λ γ → cong$ (sym (reindexEncode (Elᶠ id) C)) ∙ encodeEl (C γ)
