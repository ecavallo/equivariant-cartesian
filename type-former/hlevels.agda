{-

Definition and properties of h-contractible and h-propositional types within the fibrant
type theory.

-}
module type-former.hlevels where

open import prelude
open import axiom
open import cofibration
open import fibration.coercion
open import fibration.fibration
open import fibration.trivial
open import type-former.path
open import type-former.pi
open import type-former.sigma

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Homotopy-contractibility
------------------------------------------------------------------------------------------

IsContr : Type ℓ → Type ℓ
IsContr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

IsContrˣ : (Γ → Type ℓ) → (Γ → Type ℓ)
IsContrˣ A γ = IsContr (A γ)

opaque
  IsContrFibStr : {A : Γ → Type ℓ} (α : FibStr A) → FibStr (IsContrˣ A)
  IsContrFibStr α  =
    ΣFibStr α (ΠFibStr (α ∘ᶠˢ fst) (PathFibStr (α ∘ᶠˢ fst ∘ᶠˢ fst) snd (snd ∘ fst)))

  reindexIsContrFibStr : {A : Γ → Type ℓ} {α : FibStr A} (ρ : Δ → Γ)
    → IsContrFibStr α ∘ᶠˢ ρ ≡ IsContrFibStr (α ∘ᶠˢ ρ)
  reindexIsContrFibStr ρ =
    reindexΣFibStr _
    ∙ cong (ΣFibStr _) (reindexΠFibStr _ ∙ cong (ΠFibStr _) (reindexPathFibStr _))

IsContrᶠ : Γ ⊢ᶠType ℓ → Γ ⊢ᶠType ℓ
IsContrᶠ A .fst = IsContrˣ (A .fst)
IsContrᶠ A .snd = IsContrFibStr (A .snd)

isContrToTFibStr : (A : Γ ⊢ᶠType ℓ) (c : Γ ⊢ᶠ IsContrᶠ A) → TFibStr (A .fst)
isContrToTFibStr A c γ φ a =
  subst (A .fst γ [ φ ↦_]) (funExt λ u → c γ .snd (a u) .at0) $
  A .snd .lift 𝕚 1 (cst γ) box .fill 0
  where
  box : OpenBox 𝕚 1 (cst (A .fst γ))
  box .cof = φ
  box .tube i u = c γ .snd (a u) .at i
  box .cap .out = c γ .fst
  box .cap .out≡ u = c γ .snd (a u) .at1

TFibToIsContr : (A : Γ ⊢ᶠTriv ℓ) → Γ ⊢ᶠ IsContrᶠ (TFibToFib A)
TFibToIsContr A γ = (center , contract)
  where
  center = A .snd γ ⊥ (λ ()) .out

  ext : (a : A .fst γ) (i : 𝕀) → A .fst γ [ ∂ i ↦ _ ]
  ext a i = A .snd γ (∂ i) (∂-rec i (cst a) (cst center))

  contract : (a : A .fst γ) → a ~ center
  contract a .at i = ext a i .out
  contract a .at0 = sym (ext a 0 .out≡ (∨l refl))
  contract a .at1 = sym (ext a 1 .out≡ (∨r refl))

------------------------------------------------------------------------------------------
-- h-Propositions
------------------------------------------------------------------------------------------

IsHProp : Type ℓ → Type ℓ
IsHProp A = (a₀ a₁ : A) → a₀ ~ a₁

IsHPropˣ : (Γ → Type ℓ) → (Γ → Type ℓ)
IsHPropˣ A γ = IsHProp (A γ)

IsHPropᶠ : Γ ⊢ᶠType ℓ → Γ ⊢ᶠType ℓ
IsHPropᶠ A =
  Πᶠ A (Πᶠ (A ∘ᶠ fst) (Pathᶠ (A ∘ᶠ fst ∘ᶠ fst) (snd ∘ fst) snd))

--↓ Being contractible is an h-proposition.

IsContrIsHPropᶠ : (A : Γ ⊢ᶠType ℓ) → Γ ⊢ᶠ IsHPropᶠ (IsContrᶠ A)
IsContrIsHPropᶠ A γ (a₀ , c₀) (a₁ , c₁) = singlPath
  where
  tfib = isContrToTFibStr (A ∘ᶠ (λ (_ : 𝟙) → γ)) (λ _ → a₀ , c₀)

  module _ (i : 𝕀) (a : A .fst γ) where

    boundary : (j : 𝕀) → [ ∂ i ∨ ∂ j ] → A .fst γ
    boundary j =
      ∨-rec (∂ i) (∂ j)
        (∂-rec i (λ _ → c₀ a .at j) (λ _ → c₁ a .at j))
        (∂-rec j (λ _ → a) (λ _ → c₁ a₀ .at i))
        (∂-elim i
          (λ {refl → ∂-elim j
            (λ {refl → c₀ a .at0})
            (λ {refl → c₀ a .at1 ∙ sym (c₁ a₀ .at0)})})
          (λ {refl → ∂-elim j
            (λ {refl → c₁ a .at0})
            (λ {refl → c₁ a .at1 ∙ sym (c₁ a₀ .at1)})}))

    opaque
      total : (j : 𝕀) → A .fst γ [ ∂ i ∨ ∂ j ↦ boundary j ]
      total j = tfib tt (∂ i ∨ ∂ j) (boundary j)

    line : a ~ c₁ a₀ .at i
    line .at j = total j .out
    line .at0 = sym (total 0 .out≡ (∨r (∨l refl)))
    line .at1 = sym (total 1 .out≡ (∨r (∨r refl)))

  singlPath : (a₀ , c₀) ~ (a₁ , c₁)
  singlPath .at i .fst = c₁ a₀ .at i
  singlPath .at i .snd = line i
  singlPath .at0 =
    Σext (c₁ a₀ .at0) $ funExt $ λ a → PathExt $ λ j →
    substNaturality {B = λ b → (b' : A .fst γ) → b' ~ b} (λ _ q → q a .at j) (c₁ a₀ .at0)
    ∙ substConst (c₁ a₀ .at0) _
    ∙ sym (total 0 a j .out≡ (∨l (∨l refl)))
  singlPath .at1 =
    Σext (c₁ a₀ .at1) $ funExt $ λ a → PathExt $ λ j →
    substNaturality {B = λ b → (b' : A .fst γ) → b' ~ b} (λ _ q → q a .at j) (c₁ a₀ .at1)
    ∙ substConst (c₁ a₀ .at1) _
    ∙ sym (total 1 a j .out≡ (∨l (∨r refl)))

--↓ h-propositions are closed under universal quantification.

ΠIsHPropᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ')
  → Γ ▷ᶠ A ⊢ᶠ IsHPropᶠ B
  → Γ ⊢ᶠ IsHPropᶠ (Πᶠ A B)
ΠIsHPropᶠ A B propB γ f₀ f₁ = line
  where
  line : f₀ ~ f₁
  line .at i a = propB (γ , a) (f₀ a) (f₁ a) .at i
  line .at0 = funExt λ a → propB (γ , a) (f₀ a) (f₁ a) .at0
  line .at1 = funExt λ a → propB (γ , a) (f₀ a) (f₁ a) .at1
