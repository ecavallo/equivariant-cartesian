{-

Definition of the universe of propositional cofibrations and basic
operations involving these.

-}
{-# OPTIONS --rewriting #-}

module axioms.cofprop where

open import prelude
open import axioms.funext
open import axioms.truncation
open import axioms.shape

private variable ℓ ℓ' : Level

infixr 4 _∨_

----------------------------------------------------------------------
-- Propositional cofibrations
----------------------------------------------------------------------

postulate
  CofProp : Set
  [_] : CofProp → Set

  _∋_≈_ : (S : Shape) → ⟨ S ⟩ → ⟨ S ⟩ → CofProp
  [≈] : (S : Shape) (s t : ⟨ S ⟩) → [ S ∋ s ≈ t ] ≡ (s ≡ t)

  ⊥ : CofProp
  [⊥] : [ ⊥ ] ≡ 𝟘

  _∨_ : CofProp → CofProp → CofProp
  [∨] : ∀ φ ψ → [ φ ∨ ψ ] ≡ ∥ [ φ ] ⊎ [ ψ ] ∥

  all : (S : Shape) → (⟨ S ⟩ → CofProp) → CofProp
  [all] : ∀ S φ → [ all S φ ] ≡ ((s : ⟨ S ⟩) → [ φ s ])

  {-# REWRITE [≈] [⊥] [∨] [all] #-}

  cofIsProp : (φ : CofProp) → isProp [ φ ]

  shape→∨ : (S : Shape) (φ ψ : ⟨ S ⟩ → CofProp)
    → [ all S (λ s → φ s ∨ ψ s) ] → [ all S φ ∨ all S ψ ]

  ≈Equivariant : {S T : Shape} (σ : ShapeHom S T) → (r s : ⟨ S ⟩)
    → (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) ≡ (S ∋ r ≈ s)

  allEquivariant : {S T : Shape} (σ : ShapeHom S T) (Φ : ⟨ T ⟩ → CofProp)
    → all T Φ ≡ all S (Φ ∘ ⟪ σ ⟫)

----------------------------------------------------------------------
-- Shorthands
----------------------------------------------------------------------

∂ : 𝕀 → CofProp
∂ i = 𝕚 ∋ i ≈ 0 ∨ 𝕚 ∋ i ≈ 1

∨l : {A : Set ℓ} {B : Set ℓ'} → A → ∥ A ⊎ B ∥
∨l a = ∣ inl a ∣

∨r : {A : Set ℓ} {B : Set ℓ'} → B → ∥ A ⊎ B ∥
∨r b = ∣ inr b ∣

_,[_] : (Γ : Set ℓ) (Φ : Γ → CofProp) → Set ℓ
Γ ,[ Φ ] = Σ x ∈ Γ , [ Φ x ]

----------------------------------------------------------------------
-- Restricted types
----------------------------------------------------------------------

record _[_↦_] (A : Set ℓ) (φ : CofProp) (a : [ φ ] → A) : Set ℓ where
  constructor makeRestrict
  field
    out : A
    out≡ : ∀ u → a u ≡ out

open _[_↦_] public

restrictExt : {A : Set ℓ} {φ : CofProp} {a : [ φ ] → A}
  {z z' : A [ φ ↦ a ]}
  → z .out ≡ z' .out
  → z ≡ z'
restrictExt refl = cong (makeRestrict _) (funext λ _ → uipImp)

----------------------------------------------------------------------
-- Combining compatible partial functions
----------------------------------------------------------------------

∨-rec : {A : Set ℓ}
  (φ ψ : CofProp)
  (f : [ φ ] → A)
  (g : [ ψ ] → A)
  .(p : ∀ u v → f u ≡ g v)
  → ---------------------------
  [ φ ∨ ψ ] → A
∨-rec {A = A} φ ψ f g p =
  ∥∥-rec _ [ f ∣ g ] λ
    { (inl _) (inl _) → cong f (cofIsProp φ _ _)
    ; (inl u) (inr v) → p u v
    ; (inr v) (inl u) → sym (p u v)
    ; (inr _) (inr _) → cong g (cofIsProp ψ _ _)}

OI-rec : (r : 𝕀) {A : Set ℓ}
  → ([ 𝕚 ∋ r ≈ 0 ] → A)
  → ([ 𝕚 ∋ r ≈ 1 ] → A)
  → ---------------------------
  [ ∂ r ] → A
OI-rec r f g =
  ∨-rec (𝕚 ∋ r ≈ 0) (𝕚 ∋ r ≈ 1) f g
    (λ u v → 0≠1 (sym u ∙ v))

∨-elim : (φ ψ : CofProp)
  (P : [ φ ∨ ψ ] → Set ℓ)
  (f : (u : [ φ ]) → P (∨l u))
  (g : (v : [ ψ ]) → P (∨r v))
  .(p : (u : [ φ ]) (v : [ ψ ]) → subst P (trunc _ _) (f u) ≡ g v)
  → ---------------------------
  (w : [ φ ∨ ψ ]) → P w
∨-elim φ ψ P f g p w =
  subst P (trunc _ _) (∨-recΣ w .snd)
  where
  ∨-recΣ : [ φ ∨ ψ ] → Σ _ P
  ∨-recΣ =
    ∨-rec φ ψ
      (λ u → ∨l u , f u)
      (λ v → ∨r v , g v)
      (λ u v → Σext (trunc _ _) (p u v))

∨-elimProp : (φ ψ : CofProp)
  (P : [ φ ∨ ψ ] → Set ℓ)
  (propP : ∀ uv → isProp (P uv))
  (f : (u : [ φ ]) → P (∨l u))
  (g : (v : [ ψ ]) → P (∨r v))
  → ---------------------------
  (w : [ φ ∨ ψ ]) → P w
∨-elimProp φ ψ P propP f g =
  ∨-elim φ ψ _ f g (λ _ _ → propP _ _ _)

OI-elim : (r : 𝕀)
  {A : [ ∂ r ] → Set ℓ}
  → ((rO : [ 𝕚 ∋ r ≈ 0 ]) → A (∨l rO))
  → ((rI : [ 𝕚 ∋ r ≈ 1 ]) → A (∨r rI))
  → ---------------------------
  (rOI : [ ∂ r ]) → A rOI
OI-elim r f g =
  ∨-elim (𝕚 ∋ r ≈ 0) (𝕚 ∋ r ≈ 1) _ f g (λ {refl r≡I → 0≠1 r≡I})

∨-elimEq : (φ ψ : CofProp) {A : Set ℓ}
  {f g : [ φ ∨ ψ ] → A}
  → ((u : [ φ ]) → f (∨l u) ≡ g (∨l u))
  → ((v : [ ψ ]) → f (∨r v) ≡ g (∨r v))
  → ---------------------------
  (w : [ φ ∨ ψ ]) → f w ≡ g w
∨-elimEq φ ψ =
  ∨-elimProp φ ψ _ (λ _ → uip)

takeOutCof : {A : Set ℓ} (φ φ₀ φ₁ : CofProp)
  {f₀ : [ φ ∨ φ₀ ] → A} {f₁ : [ φ ∨ φ₁ ] → A}
  → (∀ u → f₀ (∨l u) ≡ f₁ (∨l u))
  → (∀ v₀ v₁ → f₀ (∨r v₀) ≡ f₁ (∨r v₁))
  → (∀ uv₀ uv₁ → f₀ uv₀ ≡ f₁ uv₁)
takeOutCof φ φ₀ φ₁ {f₀} {f₁} p q =
  ∨-elim φ φ₀ _
    (λ u₀ → ∨-elimEq φ φ₁
      (λ u₁ → cong f₀ (trunc _ _) ∙ p u₁)
      (λ v₁ → p u₀ ∙ (cong f₁ (trunc _ _))))
    (λ v₀ → ∨-elimEq φ φ₁
      (λ u₁ → cong f₀ (trunc _ _) ∙ p u₁)
      (λ v₁ → q v₀ v₁))
    (λ _ _ → funext λ _ → uipImp)

diagonalElim : (φ : CofProp) {P : [ φ ] → [ φ ] → Set ℓ}
  → (∀ u → P u u)
  → (∀ u v → P u v)
diagonalElim φ {P = P} f u v = subst (P u) (cofIsProp φ u v) (f u)
