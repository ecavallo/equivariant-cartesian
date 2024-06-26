{-

Definition and properties of h-contractible and h-propositional types within the fibrant
type theory.

-}
module type-former.hlevels where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.transport
open import fibration.fibration
open import fibration.trivial
open import type-former.path
open import type-former.pi
open import type-former.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Homotopy-contractibility.
------------------------------------------------------------------------------------------

IsContr : Type ℓ → Type ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a₀ ~ a)

IsContrˣ : (Γ → Type ℓ) → (Γ → Type ℓ)
IsContrˣ A = Σˣ A (Πˣ (A ∘ 𝒑) (Pathˣ (A ∘ 𝒑 ∘ 𝒑) (𝒒 ∘ 𝒑) 𝒒))

opaque
  IsContrFibStr : {A : Γ → Type ℓ} (α : FibStr A) → FibStr (IsContrˣ A)
  IsContrFibStr α  =
    ΣFibStr α (ΠFibStr (α ∘ᶠˢ 𝒑) (PathFibStr (α ∘ᶠˢ 𝒑 ∘ᶠˢ 𝒑) (𝒒 ∘ 𝒑) 𝒒))

  reindexIsContrFibStr : {A : Γ → Type ℓ} {α : FibStr A} (ρ : Δ → Γ)
    → IsContrFibStr α ∘ᶠˢ ρ ≡ IsContrFibStr (α ∘ᶠˢ ρ)
  reindexIsContrFibStr ρ =
    reindexΣFibStr _
    ∙ cong (ΣFibStr _) (reindexΠFibStr _ ∙ cong (ΠFibStr _) (reindexPathFibStr _))

IsContrᶠ : Γ ⊢ᶠType ℓ → Γ ⊢ᶠType ℓ
IsContrᶠ A .fst = IsContrˣ (A .fst)
IsContrᶠ A .snd = IsContrFibStr (A .snd)

isContrToTFibStr : (A : Γ ⊢ᶠType ℓ) (c : Γ ⊢ᶠ IsContrᶠ A) → TFibStr ∣ A ∣
isContrToTFibStr A c γ (φ , a) =
  subst (A $ᶠ γ [ φ ↦_]) (funExt λ u → c γ .snd (a u) .at1) $
  A .snd .lift 𝕚 (cst γ) 0 box .fill 1
  where
  box : OpenBox 𝕚 (cst (A $ᶠ γ)) 0
  box .cof = φ
  box .tube i u = c γ .snd (a u) .at i
  box .cap .out = c γ .fst
  box .cap .out≡ u = c γ .snd (a u) .at0

TFibToIsContr : (A : Γ ⊢ᶠTriv ℓ) → Γ ⊢ᶠ IsContrᶠ (TFibToFib A)
TFibToIsContr A γ = (center , contract)
  where
  center = A .snd γ (⊥ , λ ()) .out

  ext : (a : A .fst γ) (i : 𝕀) → A .fst γ [ ∂ i ↦ _ ]
  ext a i = A .snd γ (∂ i , ∂-rec i (cst center) (cst a))

  contract : (a : A .fst γ) → center ~ a
  contract a .at i = ext a i .out
  contract a .at0 = sym (ext a 0 .out≡ (∨l refl))
  contract a .at1 = sym (ext a 1 .out≡ (∨r refl))

------------------------------------------------------------------------------------------
-- Singletons are contractible.
------------------------------------------------------------------------------------------

singlIsContrᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  → Γ ⊢ᶠ IsContrᶠ (Singlᶠ A a)
singlIsContrᶠ A a = singlCenterᶠ A a ,ˣ λˣ (singlContractᶠ (A ∘ᶠ 𝒑) (a ∘ 𝒑) 𝒒)

------------------------------------------------------------------------------------------
-- h-Propositions.
------------------------------------------------------------------------------------------

IshProp : Type ℓ → Type ℓ
IshProp A = (a₀ a₁ : A) → a₀ ~ a₁

IshPropˣ : (Γ → Type ℓ) → (Γ → Type ℓ)
IshPropˣ A γ = IshProp (A γ)

IshPropᶠ : Γ ⊢ᶠType ℓ → Γ ⊢ᶠType ℓ
IshPropᶠ A =
  Πᶠ A (Πᶠ (A ∘ᶠ 𝒑) (Pathᶠ (A ∘ᶠ 𝒑 ∘ᶠ 𝒑) (𝒒 ∘ 𝒑) 𝒒))

--↓ Being contractible is an h-proposition.

IsContrIshPropᶠ : (A : Γ ⊢ᶠType ℓ) → Γ ⊢ᶠ IshPropᶠ (IsContrᶠ A)
IsContrIshPropᶠ A γ (a₀ , c₀) (a₁ , c₁) = singlPath
  where
  tfib = isContrToTFibStr (A ∘ᶠ cst γ) (λ _ → a₀ , c₀)

  module _ (i : 𝕀) (a : A $ᶠ γ) where

    boundary : (j : 𝕀) → [ ∂ i ∨ ∂ j ] → A $ᶠ γ
    boundary j =
      ∨-rec
        (∂-rec i (λ _ → c₀ a .at j) (λ _ → c₁ a .at j))
        (∂-rec j (λ _ → c₀ a₁ .at i) (λ _ → a))
        (∂-elim i
          (λ {refl → ∂-elim j
            (λ {refl → c₀ a .at0 ∙ sym (c₀ a₁ .at0)})
            (λ {refl → c₀ a .at1})})
          (λ {refl → ∂-elim j
            (λ {refl → c₁ a .at0 ∙ sym (c₀ a₁ .at1)})
            (λ {refl → c₁ a .at1})}))

    opaque
      total : (j : 𝕀) → A $ᶠ γ [ ∂ i ∨ ∂ j ↦ boundary j ]
      total j = tfib tt (∂ i ∨ ∂ j , boundary j)

    line : c₀ a₁ .at i ~ a
    line .at j = total j .out
    line .at0 = sym (total 0 .out≡ (∨r (∨l refl)))
    line .at1 = sym (total 1 .out≡ (∨r (∨r refl)))

  singlPath : (a₀ , c₀) ~ (a₁ , c₁)
  singlPath .at i .fst = c₀ a₁ .at i
  singlPath .at i .snd = line i
  singlPath .at0 =
    Σext (c₀ a₁ .at0) $ funExt λ a → PathExt λ j →
    substNaturality {B = λ b → ∀ b' → b ~ b'} (λ q → q a .at j) (c₀ a₁ .at0)
    ∙ substConst (c₀ a₁ .at0) _
    ∙ sym (total 0 a j .out≡ (∨l (∨l refl)))
  singlPath .at1 =
    Σext (c₀ a₁ .at1) $ funExt λ a → PathExt λ j →
    substNaturality {B = λ b → ∀ b' → b ~ b'} (λ q → q a .at j) (c₀ a₁ .at1)
    ∙ substConst (c₀ a₁ .at1) _
    ∙ sym (total 1 a j .out≡ (∨l (∨r refl)))

--↓ h-Propositions are closed under universal quantification.

ΠIshPropᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ')
  → Γ ▷ᶠ A ⊢ᶠ IshPropᶠ B
  → Γ ⊢ᶠ IshPropᶠ (Πᶠ A B)
ΠIshPropᶠ A B propB γ f₀ f₁ = line
  where
  line : f₀ ~ f₁
  line .at i a = propB (γ , a) (f₀ a) (f₁ a) .at i
  line .at0 = funExt λ a → propB (γ , a) (f₀ a) (f₁ a) .at0
  line .at1 = funExt λ a → propB (γ , a) (f₀ a) (f₁ a) .at1
