{-

Constructing a universe that classifies fibrations.

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

LocalFillStrˣ : (S : Shape)
  (A : Γ ▷⟨ S ⟩ → Type ℓ)
  → (Γ → Type ℓ)
LocalFillStrˣ S A γ = LocalFillStr S (A ∘ (γ ,_))

𝑼Fill : ∀ (@♭ ℓ) → Type (lsuc ℓ)
𝑼Fill ℓ = Σ A ∈ Type ℓ , ((@♭ S : Shape) → (S √ᴰ LocalFillStr S) A)

𝑼Fillˣ : ∀ (@♭ ℓ) → (Γ → Type (lsuc ℓ))
𝑼Fillˣ ℓ _ = 𝑼Fill ℓ

opaque
  decodeFill : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ S : Shape)
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ˣ 𝑼Fillˣ ℓ')
    → Γ ⊢ˣ LocalFillStrˣ S (fstˣ A)
  decodeFill S A =
    open√ S $♭
    appˣ (doReindex√ S (fstˣ A)) $
    λ γs → A γs .snd S

opaque
  unfolding decodeFill
  reindexDecodeFill : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ) (@♭ S : Shape)
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ˣ 𝑼Fillˣ ℓ'')
    → decodeFill S A ∘ ρ ≡ decodeFill S (A ∘ (ρ ×id))
  reindexDecodeFill ρ S A =
    reindexOpen√ S _ _ ∙
    cong♭ (open√ S) (doReindex√-∘ S (fstˣ A) (ρ ×id) _)

LocalEquivariance√ : ∀ {@♭ ℓ} {@♭ S T} (@♭ σ : Shape[ S , T ])
  (A : ⟨ T ⟩ → 𝑼Fill ℓ) → Type ℓ
LocalEquivariance√ {S = S} {T = T} σ A =
  LocalEquivariance σ
    (decodeFill T (^-counit T) A)
    (decodeFill S (^-counit S) (A ∘ ⟪ σ ⟫))

LocalEquivariance√ˣ : ∀ {@♭ ℓ ℓ'} {@♭ S T} (@♭ σ : Shape[ S , T ]) {Γ : Type ℓ}
  (A : Γ ▷⟨ T ⟩ ⊢ˣ 𝑼Fillˣ ℓ')
  → (Γ → Type ℓ')
LocalEquivariance√ˣ σ A γ = LocalEquivariance√ σ (A ∘ (γ ,_))

------------------------------------------------------------------------------------------
-- Definition of the universe and decoding function.
------------------------------------------------------------------------------------------

𝑼 : ∀ (@♭ ℓ) → Type (lsuc ℓ)
𝑼 ℓ =
  Σ A ∈ 𝑼Fill ℓ ,
  (∀ (@♭ S T) (@♭ σ : Shape[ S , T ]) → (T √ᴰ LocalEquivariance√ σ) A)

El : ∀ {@♭ ℓ} → 𝑼 ℓ → Type ℓ
El = fst ∘ fst

𝑼ˣ : ∀ (@♭ ℓ) → (Γ → Type (lsuc ℓ))
𝑼ˣ ℓ _ = 𝑼 ℓ

------------------------------------------------------------------------------------------
-- El : 𝑼 → Type is a fibration.
------------------------------------------------------------------------------------------

decodeVaries : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
  {@♭ S T : Shape} (@♭ σ : Shape[ S , T ])
  (@♭ A : Γ ▷⟨ T ⟩ ⊢ˣ 𝑼ˣ ℓ')
  → Γ ⊢ˣ LocalEquivariance√ˣ σ (fstˣ A)
decodeVaries {S = S} {T = T} σ A =
  open√ T $♭
  appˣ (doReindex√ T (fstˣ A)) $
  λ γt → A γt .snd S T σ

opaque
  ElFibStr : ∀ {@♭ ℓ} → FibStr (El {ℓ})
  ElFibStr .lift =
    ShapeIsDiscrete λ (@♭ S) →
    λ A → decodeFill S (^-counit S) (fstˣ A)
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
-- Any fibration over Γ induces an element of Γ ⊢ˣ 𝑼ˣ.
------------------------------------------------------------------------------------------

getFillStrˣ : (S : Shape)
  (A : Γ ▷⟨ S ⟩ ⊢ᶠType ℓ)
  → Γ ⊢ˣ LocalFillStrˣ S ∣ A ∣
getFillStrˣ S A γ r box = A .snd .lift S (γ ,_) r box

opaque
  encodeFillStr : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → Γ ⊢ˣ (S √ᴰ LocalFillStr S) ∘ ∣ A ∣
  encodeFillStr S A =
    appˣ (undoReindex√ S ∣ A ∣) $
    shut√ S $♭
    λ γ r box → A .snd .lift S γ r box

  reindexEncodeFillStr : ∀ {@♭ ℓ ℓ' ℓ''} (@♭ S : Shape)
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ)
    (@♭ A : Γ ⊢ᶠType ℓ'')
    → encodeFillStr S A ∘ ρ ≡ encodeFillStr S (A ∘ᶠ ρ)
  reindexEncodeFillStr S ρ A =
    cong (appˣ (undoReindex√ S ∣ A ∣ ∘ ρ))
      (sym (undoDoReindex√ S ρ _)
        ∙ cong (appˣ (undoReindex√ S ρ)) (reindexShut√ S _ ρ))
    ∙ undoReindex√-∘ S ∣ A ∣ ρ _

encodeFill : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} → @♭ (Γ ⊢ᶠType ℓ') → Γ ⊢ˣ 𝑼Fillˣ ℓ'
encodeFill A γ .fst = A $ᶠ γ
encodeFill A γ .snd S = encodeFillStr S A γ

opaque
  reindexEncodeLifts : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' → Γ)
    (@♭ A : Γ ⊢ᶠType ℓ'')
    → encodeFill A ∘ ρ ≡ encodeFill (A ∘ᶠ ρ)
  reindexEncodeLifts ρ A =
    funExt λ γ →
    Σext refl (funExt♭ λ S → cong$ (reindexEncodeFillStr S ρ A))

opaque
  unfolding encodeFillStr decodeFill
  decodeEncodeLifts : ∀ {@♭ ℓ ℓ'} {@♭ S : Shape} {@♭ Γ : Type ℓ}
    (@♭ A : Γ ▷⟨ S ⟩ ⊢ᶠType ℓ')
    → decodeFill S (encodeFill A) ≡ getFillStrˣ S A
  decodeEncodeLifts {S = S} A =
    cong♭ (open√ S) (doUndoReindex√ S _ _)
    ∙ openShut√ _ _

private
  reindexEncodeInsideDecode : ∀ {@♭ ℓ ℓ' ℓ''}
    (@♭ S : Shape)
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} (@♭ ρ : Γ' ▷⟨ S ⟩ → Γ)
    (@♭ A : Γ ⊢ᶠType ℓ'')
    → decodeFill S (encodeFill A ∘ ρ) ≡ decodeFill S (encodeFill (A ∘ᶠ ρ))
  reindexEncodeInsideDecode S ρ A =
    cong
      (subst (λ B → _ ⊢ˣ LocalFillStrˣ S B) ⦅–⦆ (decodeFill S (encodeFill A ∘ ρ)))
      uip'
    ∙ sym (substCongAssoc (λ B → _ ⊢ˣ LocalFillStrˣ S B) fstˣ (reindexEncodeLifts ρ A) _)
    ∙ congdep♭ (decodeFill S) (reindexEncodeLifts ρ A)

opaque
  encodeEquivariance : ∀ {@♭ ℓ ℓ'}
    {@♭ S T : Shape} (@♭ σ : Shape[ S , T ])
    {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → Γ ⊢ˣ (T √ᴰ LocalEquivariance√ σ) ∘ encodeFill A
  encodeEquivariance {S = S} {T = T} σ A =
    appˣ (undoReindex√ T (encodeFill A)) $
    shut√ T $♭
    λ γ r box s →
    cong (λ l → l γ (⟪ σ ⟫ r) box .fill (⟪ σ ⟫ s) .out)
      (reindexDecodeFill (encodeFill A `^ T) T (^-counit T)
        ∙ reindexEncodeInsideDecode T (^-counit T) A
        ∙ decodeEncodeLifts (A ∘ᶠ ^-counit T))
    ∙ A .snd .vary S T σ γ r box s
    ∙ cong (λ l → l (γ ∘ ⟪ σ ⟫) r (reshapeBox σ box) .fill s .out)
        (sym
          (reindexDecodeFill (encodeFill A `^ S) S (^-counit S)
            ∙ reindexEncodeInsideDecode S (^-counit S) A
            ∙ decodeEncodeLifts (A ∘ᶠ ^-counit S)))

opaque
  encode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} → @♭ (Γ ⊢ᶠType ℓ') → (Γ ⊢ˣ 𝑼ˣ ℓ')
  encode {ℓ' = ℓ'} {Γ} A = encoding
    where
    encoding : Γ ⊢ˣ 𝑼ˣ ℓ'
    encoding γ .fst = encodeFill A γ
    encoding γ .snd S T σ = encodeEquivariance σ A γ

------------------------------------------------------------------------------------------
-- Inverse conditions for the correspondence between Γ ⊢ᶠType ℓ' and Γ ⊢ˣ 𝑼ˣ ℓ'.
------------------------------------------------------------------------------------------

opaque
  unfolding encode ElFibStr
  decodeEncode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ A : Γ ⊢ᶠType ℓ')
    → decode (encode A) ≡ A
  decodeEncode A =
    Σext refl $
    FibStrExt {α₀ = ElFibStr ∘ᶠˢ (encode A)} $
    ShapeIsDiscrete λ (@♭ S) γ r box s →
    cong (λ lifter → lifter r box .fill s .out) (mainLemma S γ)
    where
    mainLemma : ∀ (@♭ S) γ →
      decodeFill S (^-counit S) (encodeFill A ∘ γ) ≡ getFillStrˣ S (A ∘ᶠ ^-counit S) γ
    mainLemma S γ =
      cong$ (reindexDecodeFill (encodeFill A `^ S) S (^-counit S))
      ∙ cong$ (reindexEncodeInsideDecode S (^-counit S) A)
      ∙ cong$ (decodeEncodeLifts (A ∘ᶠ ^-counit S))

opaque
  𝑼Ext : ∀ {@♭ ℓ} {C C' : 𝑼 ℓ} → C .fst ≡ C' .fst → C ≡ C'
  𝑼Ext eq =
    Σext eq $
    funExt♭ λ S → funExt♭ λ T → funExt♭ λ σ →
    √ᴰPreservesProp T
      (LocalEquivariance√ σ)
      (λ _ _ _ → funExt' $ funExt' $ funExt' uip')
      _ _ _

opaque
  unfolding encode
  reindexEncode : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Δ : Type ℓ} {@♭ Γ : Type ℓ'}
    (@♭ A : Γ ⊢ᶠType ℓ'') (@♭ ρ : Δ → Γ)
    → encode A ∘ ρ ≡ encode (A ∘ᶠ ρ)
  reindexEncode A ρ =
    funExt' $ 𝑼Ext $ cong$ $ reindexEncodeLifts ρ A

opaque
  unfolding encode ElFibStr encodeFillStr decodeFill
  encodeEl : ∀ {@♭ ℓ} → (C : 𝑼 ℓ) → encode (Elᶠ id) C ≡ C
  encodeEl {ℓ = ℓ} =
    λ C → 𝑼Ext $ Σext refl (funExt♭ λ S → cong$ (lemma S))
    where
    get√FillStr : (@♭ S : Shape) (C : 𝑼 ℓ) → (S √ᴰ LocalFillStr S) (El C)
    get√FillStr S C = C .fst .snd S

    lemma : (@♭ S : Shape) → encodeFillStr S (Elᶠ id) ≡ get√FillStr S
    lemma S =
      cong (appˣ (undoReindex√ S El))
        (cong♭ (shut√ S)
          (reindexDecodeFill (fst `^ S) S (^-counit S)
            ∙ cong♭ (open√ S)
                (sym (doReindex√-∘ S El (^-counit S) (get√FillStr S ∘ ^-counit S))))
          ∙ sym (shutOpen√ S (appˣ (doReindex√ S El) (get√FillStr S))))
      ∙ undoDoReindex√ S El (get√FillStr S)

opaque
  encodeDecode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ C : Γ ⊢ˣ 𝑼ˣ ℓ') → encode (decode C) ≡ C
  encodeDecode C = funExt λ γ → cong$ (sym (reindexEncode (Elᶠ id) C)) ∙ encodeEl (C γ)
