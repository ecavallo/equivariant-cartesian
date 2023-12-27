{-

Definitions of contractibility and equivalences.

-}
module type-former.equiv where

open import prelude
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.coercion
open import fibration.fibration
open import fibration.trivial
open import type-former.hlevels
open import type-former.path
open import type-former.pi
open import type-former.sigma

private variable
  ℓ ℓ' ℓ'' : Level
  Γ Δ : Type ℓ

infix 4 _≃_

------------------------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------------------------

IsEquiv : {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type (ℓ ⊔ ℓ')
IsEquiv f = ∀ b → IsContr (Fiber f b)

_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) IsEquiv

IsEquivˣ : {A : Γ → Type ℓ} {B : Γ → Type ℓ'} (f : Γ ⊢ˣ A →ˣ B)
  → Γ → Type (ℓ ⊔ ℓ')
IsEquivˣ f = Πˣ _ (IsContrˣ (Fiberˣ (f ∘ 𝒑) 𝒒))

_≃ˣ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
A ≃ˣ B = Σˣ (A →ˣ B) (IsEquivˣ snd)

--↓ An isomorphism composed with an equivalence is an equivalence.

equiv∘iso : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → A ≅ B → B ≃ C → A ≃ C
equiv∘iso iso e .fst = e .fst ∘ iso .to
equiv∘iso iso e .snd c = contractor
  where
  invertFiber : ∀ c → Fiber (e .fst) c → Fiber (e .fst ∘ iso .to) c
  invertFiber c (b , p) .fst = iso .from b
  invertFiber c (b , p) .snd .at = p .at
  invertFiber c (b , p) .snd .at0 =
    p .at0 ∙ cong (e .fst) (sym (cong$ (iso .inv₂)))
  invertFiber c (b , p) .snd .at1 = p .at1

  contractor : IsContr (Fiber (e .fst ∘ iso .to) c)
  contractor .fst = invertFiber c (e .snd c .fst)
  contractor .snd (a , p) =
    subst
      (_~ _)
      (FiberExt (cong$ (iso .inv₁)) (λ _ → refl))
      (congPath
        (invertFiber c)
        (e .snd c .snd (iso .to a , p)))

------------------------------------------------------------------------------------------
-- Fibrancy of the type of equivalences between two fibrant types
------------------------------------------------------------------------------------------

opaque
  IsEquivFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    (f : Γ ⊢ˣ A →ˣ B) → FibStr (IsEquivˣ f)
  IsEquivFibStr α β f =
    ΠFibStr β (IsContrFibStr (FiberFibStr (α ∘ᶠˢ 𝒑) (β ∘ᶠˢ 𝒑) (f ∘ 𝒑) 𝒒))

  reindexIsEquivFibStr : {A : Γ → Type ℓ} {α : FibStr A} {B : Γ → Type ℓ'} {β : FibStr B}
    {f : Γ ⊢ˣ A →ˣ B}
    (ρ : Δ → Γ)
    → IsEquivFibStr α β f ∘ᶠˢ ρ ≡ IsEquivFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ ρ) (f ∘ ρ)
  reindexIsEquivFibStr ρ =
    reindexΠFibStr _
    ∙ cong (ΠFibStr _)
        (reindexIsContrFibStr _
          ∙ cong IsContrFibStr (reindexFiberFibStr _))

IsEquivᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') (f : Γ ⊢ᶠ A →ᶠ B)
  → Γ ⊢ᶠType (ℓ ⊔ ℓ')
IsEquivᶠ A B f .fst = IsEquivˣ f
IsEquivᶠ A B f .snd = IsEquivFibStr (A .snd) (B .snd) f

opaque
  EquivFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ → Type ℓ'} (β : FibStr B)
    → FibStr (A ≃ˣ B)
  EquivFibStr α β =
    ΣFibStr (ΠFibStr α (β ∘ᶠˢ 𝒑)) (IsEquivFibStr (α ∘ᶠˢ 𝒑) (β ∘ᶠˢ 𝒑) 𝒒)

  reindexEquivFibStr : {A : Γ → Type ℓ} {α : FibStr A} {B : Γ → Type ℓ'} {β : FibStr B}
    (ρ : Δ → Γ) → EquivFibStr α β ∘ᶠˢ ρ ≡ EquivFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ ρ)
  reindexEquivFibStr ρ =
    reindexΣFibStr _
    ∙ cong₂ (λ α β → ΣFibStr α β) (reindexΠFibStr _) (reindexIsEquivFibStr _)

_≃ᶠ_ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') → Γ ⊢ᶠType (ℓ ⊔ ℓ')
(A ≃ᶠ B) .fst = (A .fst) ≃ˣ (B .fst)
(A ≃ᶠ B) .snd = EquivFibStr (A .snd) (B .snd)

reindexEquivᶠ : {A : Γ ⊢ᶠType ℓ} {B : Γ ⊢ᶠType ℓ'}
  (ρ : Δ → Γ) → (A ≃ᶠ B) ∘ᶠ ρ ≡ (A ∘ᶠ ρ) ≃ᶠ (B ∘ᶠ ρ)
reindexEquivᶠ ρ = Σext refl (reindexEquivFibStr _)

------------------------------------------------------------------------------------------
-- Being an equivalence is an h-proposition
------------------------------------------------------------------------------------------

opaque
  IsEquivIsHPropᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') (f : Γ ⊢ᶠ A →ᶠ B)
    → Γ ⊢ᶠ IsHPropᶠ (IsEquivᶠ A B f)
  IsEquivIsHPropᶠ A B f =
    ΠIsHPropᶠ
      B
      (IsContrᶠ (Fiberᶠ (A ∘ᶠ 𝒑) (B ∘ᶠ 𝒑) (f ∘ 𝒑) 𝒒))
      (IsContrIsHPropᶠ (Fiberᶠ (A ∘ᶠ 𝒑) (B ∘ᶠ 𝒑) (f ∘ 𝒑) 𝒒))

--↓ To construct a path between equivalences, it suffices to build a path between the
--↓ underlying functions.

opaque
  equivPathᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') (e₀ e₁ : Γ ⊢ᶠ A ≃ᶠ B)
    → Γ ⊢ᶠ Pathᶠ (A →ᶠ B) (fstˣ e₀) (fstˣ e₁)
    → Γ ⊢ᶠ Pathᶠ (A ≃ᶠ B) e₀ e₁
  equivPathᶠ A B e₀ e₁ p =
    appˣ
      (Jᶠ (A →ᶠ B) (fstˣ e₁)
        (Πᶠ (IsEquivᶠ (A ∘ᶠ 𝒑) (B ∘ᶠ 𝒑) (fstˣ 𝒒))
          (Pathᶠ (A ≃ᶠ B ∘ᶠ 𝒑 ∘ᶠ 𝒑)
            (fstˣ (𝒒 ∘ 𝒑) ,ˣ 𝒒)
            (e₁ ∘ 𝒑 ∘ 𝒑)))
        (λˣ $
          congPathˣ
            (λˣ (fstˣ e₁ ∘ 𝒑 ∘ 𝒑 ,ˣ 𝒒))
            (appˣ (appˣ (IsEquivIsHPropᶠ A B (fstˣ e₁) ∘ 𝒑) 𝒒) (sndˣ e₁ ∘ 𝒑)))
        (fstˣ e₀ ,ˣ p))
      (sndˣ e₀)

------------------------------------------------------------------------------------------
-- A map f : A → B between fibrant types is an equivalence if and only if its fiber family
-- is a trivial fibration
------------------------------------------------------------------------------------------

equivToFiberTFib : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ')
  (e : Γ ⊢ᶠ A ≃ᶠ B) → TFibStr (Fiberˣ (fstˣ e ∘ 𝒑) 𝒒)
equivToFiberTFib A B e =
  isContrToTFibStr
    (Fiberᶠ (A ∘ᶠ 𝒑) (B ∘ᶠ 𝒑) (fstˣ e ∘ 𝒑) 𝒒)
    (appˣ (sndˣ (e ∘ 𝒑)) 𝒒)

fiberTFibToIsEquiv : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') {f : Γ ⊢ᶠ A →ᶠ B}
  → TFibStr (Fiberˣ (f ∘ 𝒑) 𝒒) → Γ ⊢ᶠ IsEquivᶠ A B f
fiberTFibToIsEquiv A B c = curry (TFibToIsContr (_ , c))

------------------------------------------------------------------------------------------
-- Identity and coercion maps are equivalences
------------------------------------------------------------------------------------------

--- TODO use existing proof of singleton contractibility
idEquiv : {A : Type ℓ} → FibStr (λ (_ : 𝟙) → A) → A ≃ A
idEquiv α .fst a = a
idEquiv α .snd a .fst = (a , refl~ a)
idEquiv {A = A} α .snd a .snd (a' , p) = h
  where
  qBox : (i : 𝕀) → OpenBox 𝕚 1 (cst A)
  qBox i .cof = ∂ i
  qBox i .tube j = ∂-rec i (λ {refl → p .at j}) (λ {refl → a})
  qBox i .cap .out = a
  qBox i .cap .out≡ = ∂-elim i (λ {refl → p .at1}) (λ {refl → refl})

  q : (i : 𝕀) → Filler (qBox i)
  q i = α .lift 𝕚 1 (cst _) (qBox i)

  h : (a' , p) ~ (a , refl~ a)
  h .at i .fst = q i .fill 0 .out
  h .at i .snd = path (λ j → q i .fill j .out) refl (q i .cap≡)
  h .at0 =
    FiberExt
      (sym (q 0 .fill 0 .out≡ (∨l refl)) ∙ p .at0)
      (λ j → sym (q 0 .fill j .out≡ (∨l refl)))
  h .at1 =
    FiberExt
      (sym (q 1 .fill 0 .out≡ (∨r refl)))
      (λ j → sym (q 1 .fill j .out≡ (∨r refl)))

idEquivᶠ : (A : Γ ⊢ᶠType ℓ) → Γ ⊢ᶠ A ≃ᶠ A
idEquivᶠ (_ , α) γ = idEquiv (α ∘ᶠˢ cst γ)

opaque
  coerceEquiv : (S : Shape)
    (A : ⟨ S ⟩ ⊢ᶠType ℓ )
    (r s : ⟨ S ⟩) → (A $ᶠ r) ≃ (A $ᶠ s)
  coerceEquiv S A r s =
    Coerce.coerce S r ((A ∘ᶠ cst r) ≃ᶠ A) (idEquivᶠ A r) s

  coerceEquivCap : (S : Shape)
    (A : ⟨ S ⟩ ⊢ᶠType ℓ)
    (r : ⟨ S ⟩) → coerceEquiv S A r r ≡ idEquivᶠ A r
  coerceEquivCap S A r =
    Coerce.cap≡ S r
      ((A ∘ᶠ cst r) ≃ᶠ A)
      (idEquivᶠ A r)

  coerceEquivVary : ∀ {ℓ} {S T : Shape} (σ : ShapeHom S T)
    (A : ⟨ T ⟩ ⊢ᶠType ℓ)
    (r s : ⟨ S ⟩)
    → coerceEquiv T A (⟪ σ ⟫ r) (⟪ σ ⟫ s) ≡ coerceEquiv S (A ∘ᶠ ⟪ σ ⟫) r s
  coerceEquivVary {S = S} σ A r s =
    coerceVary σ r
      ((A ∘ᶠ cst (⟪ σ ⟫ r)) ≃ᶠ A)
      (idEquivᶠ A (⟪ σ ⟫ r))
      s
    ∙
    cong
      (λ β → Coerce.coerce S r (_ ≃ˣ _ , β) (idEquivᶠ A (⟪ σ ⟫ r)) s)
      (Σeq₂ (reindexEquivᶠ ⟪ σ ⟫) refl)
