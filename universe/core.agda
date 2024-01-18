{-

Constructing a universe that classifies fibrations

-}
module universe.core where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import tiny.dependent
open import fibration.fibration
open import type-former.sigma

private variable
  ℓ ℓ' : Level
  Γ : Type ℓ

open DependentTiny

hasLiftsˣ : (S : Shape)
  (A : Γ ▷⟨ S ⟩ → Type ℓ)
  → (Γ → Type ℓ)
hasLiftsˣ S A γ = hasLifts S (A ∘ (γ ,_))

𝑼Lifts : ∀ (@♭ ℓ) → Type (lsuc ℓ)
𝑼Lifts ℓ = Σ A ∈ Type ℓ , ((@♭ S : Shape) → (S √ᴰ hasLifts S) A)

𝑼Liftsˣ : ∀ (@♭ ℓ) → (Γ → Type (lsuc ℓ))
𝑼Liftsˣ ℓ _ = 𝑼Lifts ℓ

opaque
  decodeLifts : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ S : Shape)
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ˣ 𝑼Liftsˣ ℓ')
    → Γ ⊢ˣ hasLiftsˣ S (fstˣ A)
  decodeLifts S A =
    open√ S $♭
    appˣ (doReindex√ S (fstˣ A)) $
    λ γs → A γs .snd S

opaque
  unfolding decodeLifts
  reindexDecodeLifts : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ) (@♭ S : Shape)
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ˣ 𝑼Liftsˣ ℓ'')
    → decodeLifts S A ∘ ρ ≡ decodeLifts S (A ∘ (ρ ×id))
  reindexDecodeLifts ρ S A =
    reindexOpen√ S _ _ ∙
    cong♭ (open√ S) (doReindex√-∘ S (fstˣ A) (ρ ×id) _)

hasVaries√ : ∀ {@♭ ℓ} {@♭ S T} (@♭ σ : ShapeHom S T)
  (A : ⟨ T ⟩ → 𝑼Lifts ℓ) → Type ℓ
hasVaries√ {S = S} {T = T} σ A =
  hasVaries σ (fst ∘ A)
    (decodeLifts T (^-counit T) A)
    (decodeLifts S (^-counit S) (A ∘ ⟪ σ ⟫))

opaque
  hasVaries√IsStrictProp : ∀ {@♭ ℓ} {@♭ S T} (@♭ σ : ShapeHom S T)
    (A : ⟨ T ⟩ → 𝑼Lifts ℓ)
    → isStrictProp (hasVaries√ σ A)
  hasVaries√IsStrictProp σ A v v' =
    funExt' $ funExt' $ funExt' uip'

hasVaries√ˣ : ∀ {@♭ ℓ ℓ'} {@♭ S T} (@♭ σ : ShapeHom S T) {Γ : Type ℓ}
  (A : Γ ▷⟨ T ⟩ ⊢ˣ 𝑼Liftsˣ ℓ')
  → (Γ → Type ℓ')
hasVaries√ˣ σ A γ = hasVaries√ σ (A ∘ (γ ,_))

𝑼 : ∀ (@♭ ℓ) → Type (lsuc ℓ)
𝑼 ℓ = Σ A ∈ 𝑼Lifts ℓ , (∀ (@♭ S T) (@♭ σ : ShapeHom S T) → (T √ᴰ hasVaries√ σ) A)

El : ∀ {@♭ ℓ} → 𝑼 ℓ → Type ℓ
El = fst ∘ fst

𝑼ˣ : ∀ (@♭ ℓ) → (Γ → Type (lsuc ℓ))
𝑼ˣ ℓ _ = 𝑼 ℓ

decodeVaries : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
  {@♭ S T : Shape} (@♭ σ : ShapeHom S T)
  (@♭ A : Γ ▷⟨ T ⟩ ⊢ˣ 𝑼ˣ ℓ')
  → Γ ⊢ˣ hasVaries√ˣ σ (fstˣ A)
decodeVaries {S = S} {T = T} σ A =
  open√ T $♭
  appˣ (doReindex√ T (fstˣ A)) $
  λ γt → A γt .snd S T σ

------------------------------------------------------------------------------------------
-- El : 𝑼 → Type is a fibration
------------------------------------------------------------------------------------------

opaque
  ElFibStr : ∀ {@♭ ℓ} → FibStr (El {ℓ})
  ElFibStr .lift =
    ShapeIsDiscrete λ (@♭ S) →
    λ A → decodeLifts S (^-counit S) (fstˣ A)
  ElFibStr .vary =
    ShapeIsDiscrete λ (@♭ S) →
    ShapeIsDiscrete λ (@♭ T) →
    ShapeHomIsDiscrete λ (@♭ σ) →
    decodeVaries σ (^-counit T)

Elˣ : ∀ {@♭ ℓ} → (Γ ⊢ˣ 𝑼ˣ ℓ) → (Γ → Type ℓ)
Elˣ = El ∘_

Elᶠ : ∀ {@♭ ℓ} → (Γ ⊢ˣ 𝑼ˣ ℓ) → Γ ⊢ᶠType ℓ
Elᶠ = (El , ElFibStr) ∘ᶠ_

decode = Elᶠ

------------------------------------------------------------------------------------------
-- Any fibration induces a map into 𝑼
------------------------------------------------------------------------------------------

getFibLiftsˣ : (S : Shape)
  (A : Γ ▷⟨ S ⟩ ⊢ᶠType ℓ)
  → Γ ⊢ˣ hasLiftsˣ S ∣ A ∣
getFibLiftsˣ S A γ r box = A .snd .lift S (γ ,_) r box

opaque
  encodeHasLifts : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → Γ ⊢ˣ (S √ᴰ hasLifts S) ∘ ∣ A ∣
  encodeHasLifts S A =
    appˣ (undoReindex√ S ∣ A ∣) $
    shut√ S $♭
    λ γ r box → A .snd .lift S γ r box

  reindexEncodeHasLifts : ∀ {@♭ ℓ ℓ' ℓ''} (@♭ S : Shape)
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ)
    (@♭ A : Γ ⊢ᶠType ℓ'')
    → encodeHasLifts S A ∘ ρ ≡ encodeHasLifts S (A ∘ᶠ ρ)
  reindexEncodeHasLifts S ρ A =
    cong (appˣ (undoReindex√ S ∣ A ∣ ∘ ρ))
      (sym (undoDoReindex√ S ρ _)
        ∙ cong (appˣ (undoReindex√ S ρ)) (reindexShut√ S _ ρ))
    ∙ undoReindex√-∘ S ∣ A ∣ ρ _

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
  unfolding encodeHasLifts decodeLifts
  decodeEncodeLifts : ∀ {@♭ ℓ ℓ'} {@♭ S : Shape} {@♭ Γ : Type ℓ}
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ᶠType ℓ')
    → decodeLifts S (encodeLifts A) ≡ getFibLiftsˣ S A
  decodeEncodeLifts {S = S} A =
    cong♭ (open√ S) (doUndoReindex√ S _ _)
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
  encodeHasVaries : ∀ {@♭ ℓ ℓ'}
    {@♭ S T : Shape} (@♭ σ : ShapeHom S T)
    {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → Γ ⊢ˣ (T √ᴰ hasVaries√ σ) ∘ encodeLifts A
  encodeHasVaries {S = S} {T = T} σ A =
    appˣ (undoReindex√ T (encodeLifts A)) $
    shut√ T $♭
    λ γ r box s →
    cong (λ l → l γ (⟪ σ ⟫ r) box .fill (⟪ σ ⟫ s) .out)
      (reindexDecodeLifts (encodeLifts A `^ T) T (^-counit T)
        ∙ reindexEncodeInsideDecode T (^-counit T) A
        ∙ decodeEncodeLifts (A ∘ᶠ ^-counit T))
    ∙ A .snd .vary S T σ γ r box s
    ∙ cong (λ l → l (γ ∘ ⟪ σ ⟫) r (reshapeBox σ box) .fill s .out)
        (sym
          (reindexDecodeLifts (encodeLifts A `^ S) S (^-counit S)
            ∙ reindexEncodeInsideDecode S (^-counit S) A
            ∙ decodeEncodeLifts (A ∘ᶠ ^-counit S)))

opaque
  encode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} → @♭ (Γ ⊢ᶠType ℓ') → (Γ ⊢ˣ 𝑼ˣ ℓ')
  encode {ℓ' = ℓ'} {Γ} A = encoding
    where
    encoding : Γ ⊢ˣ 𝑼ˣ ℓ'
    encoding γ .fst = encodeLifts A γ
    encoding γ .snd S T σ = encodeHasVaries σ A γ

------------------------------------------------------------------------------------------
-- Inverse conditions for the correspondence between Fib Γ and Γ ⊢ˣ 𝑼ˣ
------------------------------------------------------------------------------------------

opaque
  unfolding encode ElFibStr
  decodeEncode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → decode (encode A) ≡ A
  decodeEncode A =
    Σext refl $
    FibStrExt {α = ElFibStr ∘ᶠˢ (encode A)} $
    ShapeIsDiscrete λ (@♭ S) γ r box s →
    cong (λ lifter → lifter r box .fill s .out) (mainLemma S γ)
    where
    mainLemma : ∀ (@♭ S) γ →
      decodeLifts S (^-counit S) (encodeLifts A ∘ γ) ≡ getFibLiftsˣ S (A ∘ᶠ ^-counit S) γ
    mainLemma S γ =
      cong$ (reindexDecodeLifts (encodeLifts A `^ S) S (^-counit S))
      ∙ cong$ (reindexEncodeInsideDecode S (^-counit S) A)
      ∙ cong$ (decodeEncodeLifts (A ∘ᶠ ^-counit S))

opaque
  𝑼Ext : ∀ {@♭ ℓ} {C C' : 𝑼 ℓ} → C .fst ≡ C' .fst → C ≡ C'
  𝑼Ext eq =
    Σext eq $
    funExt♭ λ S → funExt♭ λ T → funExt♭ λ σ →
    √ᴰPreservesProp T (hasVaries√ σ) (λ _ → hasVaries√IsStrictProp σ _) _ _ _

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

    lemma : (@♭ S : Shape) → encodeHasLifts S (Elᶠ id) ≡ get√Lifts S
    lemma S =
      cong (appˣ (undoReindex√ S El))
        (cong♭ (shut√ S)
          (reindexDecodeLifts (fst `^ S) S (^-counit S)
            ∙ cong♭ (open√ S)
                (sym (doReindex√-∘ S El (^-counit S) (get√Lifts S ∘ ^-counit S))))
          ∙ sym (shutOpen√ S (appˣ (doReindex√ S El) (get√Lifts S))))
      ∙ undoDoReindex√ S El (get√Lifts S)

opaque
  encodeDecode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ C : Γ ⊢ˣ 𝑼ˣ ℓ') → encode (decode C) ≡ C
  encodeDecode C = funExt λ γ → cong$ (sym (reindexEncode (Elᶠ id) C)) ∙ encodeEl (C γ)
