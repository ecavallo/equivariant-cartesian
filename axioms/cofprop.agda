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
  [⊥] : [ ⊥ ] ≡ ∅

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

∂ : Int → CofProp
∂ i = int ∋ i ≈ O ∨ int ∋ i ≈ I

_,[_] : ∀ {ℓ} (Γ : Set ℓ) (Φ : Γ → CofProp) → Set ℓ
Γ ,[ Φ ] = Σ x ∈ Γ , [ Φ x ]

----------------------------------------------------------------------
-- Restricted types
----------------------------------------------------------------------

record _[_↦_] {ℓ} (A : Set ℓ) (φ : CofProp) (a : [ φ ] → A) : Set ℓ where
  constructor makeRestrict
  field
    out : A
    out≡ : ∀ u → a u ≡ out

open _[_↦_] public

restrictExt : ∀ {ℓ} {A : Set ℓ} {φ : CofProp} {a : [ φ ] → A}
  {z z' : A [ φ ↦ a ]}
  → z .out ≡ z' .out
  → z ≡ z'
restrictExt refl = cong (makeRestrict _) (funext λ _ → uipImp)

----------------------------------------------------------------------
-- Combining compatible partial functions
----------------------------------------------------------------------

∨-rec : ∀ {ℓ} {A : Set ℓ}
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
    ; (inr v) (inl u) → symm (p u v)
    ; (inr _) (inr _) → cong g (cofIsProp ψ _ _)}

OI-rec : ∀ {ℓ}
  (r : Int)
  {A : Set ℓ}
  → ([ int ∋ r ≈ O ] → A)
  → ([ int ∋ r ≈ I ] → A)
  → ---------------------------
  [ int ∋ r ≈ O ∨ int ∋ r ≈ I ] → A
OI-rec r f g =
  ∨-rec (int ∋ r ≈ O) (int ∋ r ≈ I) f g
    (λ u v → O≠I (symm u ∙ v))

∨-elim : ∀ {ℓ}
  (φ ψ : CofProp)
  (P : [ φ ∨ ψ ] → Set ℓ)
  (f : (u : [ φ ]) → P ∣ inl u ∣)
  (g : (v : [ ψ ]) → P ∣ inr v ∣)
  .(p : (u : [ φ ]) (v : [ ψ ]) → subst P (trunc _ _) (f u) ≡ g v)
  → ---------------------------
  (w : [ φ ∨ ψ ]) → P w
∨-elim φ ψ P f g p w =
  subst P (trunc _ _) (∨-recΣ w .snd)
  where
  ∨-recΣ : [ φ ∨ ψ ] → Σ _ P
  ∨-recΣ =
    ∨-rec φ ψ
      (λ u → ∣ inl u ∣ , f u)
      (λ v → ∣ inr v ∣ , g v)
      (λ u v → Σext (trunc _ _) (p u v))

∨-elimProp : ∀ {ℓ}
  (φ ψ : CofProp)
  (P : [ φ ∨ ψ ] → Set ℓ)
  (propP : ∀ uv → isProp (P uv))
  (f : (u : [ φ ]) → P ∣ inl u ∣)
  (g : (v : [ ψ ]) → P ∣ inr v ∣)
  → ---------------------------
  (w : [ φ ∨ ψ ]) → P w
∨-elimProp φ ψ P propP f g =
  ∨-elim φ ψ _ f g (λ _ _ → propP _ _ _)

OI-elim : ∀ {ℓ}
  (r : Int)
  {A : [ int ∋ r ≈ O ∨ int ∋ r ≈ I ] → Set ℓ}
  → ((rO : [ int ∋ r ≈ O ]) → A ∣ inl rO ∣)
  → ((rI : [ int ∋ r ≈ I ]) → A ∣ inr rI ∣)
  → ---------------------------
  (rOI : [ int ∋ r ≈ O ∨ int ∋ r ≈ I ]) → A rOI
OI-elim r f g =
  ∨-elim (int ∋ r ≈ O) (int ∋ r ≈ I) _ f g (λ {refl r≡I → O≠I r≡I})

∨-elimEq : ∀ {ℓ}
  (φ ψ : CofProp) {A : Set ℓ}
  {f g : [ φ ∨ ψ ] → A}
  → ((u : [ φ ]) → f ∣ inl u ∣ ≡ g ∣ inl u ∣)
  → ((v : [ ψ ]) → f ∣ inr v ∣ ≡ g ∣ inr v ∣)
  → ---------------------------
  (w : [ φ ∨ ψ ]) → f w ≡ g w
∨-elimEq φ ψ =
  ∨-elimProp φ ψ _ (λ _ → uip)

takeOutCof : ∀ {ℓ} {A : Set ℓ} (φ φ₀ φ₁ : CofProp)
  {f₀ : [ φ ∨ φ₀ ] → A} {f₁ : [ φ ∨ φ₁ ] → A}
  → (∀ u → f₀ ∣ inl u ∣ ≡ f₁ ∣ inl u ∣)
  → (∀ v₀ v₁ → f₀ ∣ inr v₀ ∣ ≡ f₁ ∣ inr v₁ ∣)
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

diagonalElim : ∀ {ℓ} (φ : CofProp) {P : [ φ ] → [ φ ] → Set ℓ}
  → (∀ u → P u u)
  → (∀ u v → P u v)
diagonalElim φ {P = P} f u v = subst (P u) (cofIsProp φ u v) (f u)
