{-

Definition of the universe of cofibrant propositions and basic
operations on these.

-}
{-# OPTIONS --rewriting #-}

module axioms.cofprop where

open import prelude
open import axioms.funext
open import axioms.truncation
open import axioms.shape

infixr 4 _∨_

----------------------------------------------------------------------
-- Cofibrant propositions
----------------------------------------------------------------------

postulate
  CofProp : Set
  [_] : CofProp → Set

  _∋_≈_ : (S : Shape) → ⟨ S ⟩ → ⟨ S ⟩ → CofProp
  [≈] : (S : Shape) (s t : ⟨ S ⟩) → [ S ∋ s ≈ t ] ≡ (s ≡ t)

  _∨_ : CofProp → CofProp → CofProp
  [∨] : ∀ φ ψ → [ φ ∨ ψ ] ≡ ∥ [ φ ] ⊎ [ ψ ] ∥

  all : (S : Shape) → (⟨ S ⟩ → CofProp) → CofProp
  [all] : ∀ S φ → [ all S φ ] ≡ ((s : ⟨ S ⟩) → [ φ s ])

  {-# REWRITE [≈] [∨] [all] #-}

  cofIsProp : (φ : CofProp) → (u v : [ φ ]) → u ≡ v

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

_[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : CofProp) → ([ φ ] → A) → Set ℓ
A [ φ ↦ f ] = Σ a ∈ A , ∀ u → f u ≡ a

res : ∀ {ℓ} (Γ : Set ℓ) (Φ : Γ → CofProp) → Set ℓ
res Γ Φ = Σ x ∈ Γ , [ Φ x ]

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
  ∥∥-rec _ h λ
    { (inl _) (inl _) → cong f (cofIsProp φ _ _)
    ; (inl u) (inr v) → p u v
    ; (inr v) (inl u) → symm (p u v)
    ; (inr _) (inr _) → cong g (cofIsProp ψ _ _)}
  where
  h : [ φ ] ⊎ [ ψ ] → A
  h (inl u) = f u
  h (inr v) = g v

OI-rec : ∀ {ℓ}
  (r : Int)
  {A : Set ℓ}
  → ([ int ∋ r ≈ O ] → A)
  → ([ int ∋ r ≈ I ] → A)
  → ---------------------------
  [ int ∋ r ≈ O ∨ int ∋ r ≈ I ] → A
OI-rec r f g =
  ∨-rec (int ∋ r ≈ O) (int ∋ r ≈ I) f g (λ {refl r≡I → O≠I r≡I})

∨-elim : ∀ {ℓ}
  (φ ψ : CofProp)
  (P : [ φ ∨ ψ ] → Set ℓ)
  (f : (u : [ φ ]) → P ∣ inl u ∣)
  (g : (v : [ ψ ]) → P ∣ inr v ∣)
  .(p : (u : [ φ ]) (v : [ ψ ]) → subst P (trunc _ _) (f u) ≡ g v)
  → ---------------------------
  (w : [ φ ∨ ψ ]) → P w
∨-elim φ ψ P f g p =
  ∥∥-elim _ h λ
    { (inl u) (inl u') →
      trans
        (congdep f (cofIsProp φ u u'))
        (trans
          (symm (substCongAssoc P (∣_∣ ∘ inl) (cofIsProp φ u u') _))
          (cong (λ r → subst P r (f u))
            (uip (trunc ∣ inl u ∣ ∣ inl u' ∣) (cong (∣_∣ ∘ inl) (cofIsProp φ u u')))))
    ; (inl u) (inr v) →
      p u v
    ; (inr v) (inl u) →
      adjustSubstEq P
        refl (trunc ∣ inl u ∣ ∣ inr v ∣)
        (trunc ∣ inr v ∣ ∣ inl u ∣) refl
        (symm (p u v))
    ; (inr v) (inr v') →
      trans
        (congdep g (cofIsProp ψ v v'))
        (trans
          (symm (substCongAssoc P (∣_∣ ∘ inr) (cofIsProp ψ v v') _))
          (cong (λ r → subst P r (g v))
            (uip (trunc ∣ inr v ∣ ∣ inr v' ∣) (cong (∣_∣ ∘ inr) (cofIsProp ψ v v')))))
    }
  where
  h : (z : [ φ ] ⊎ [ ψ ]) → P ∣ z ∣
  h (inl u) = f u
  h (inr v) = g v

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
∨-elimEq φ ψ p q =
  ∨-elim φ ψ _ p q (λ _ _ → uipImp)

takeOutCof : ∀ {ℓ} {A : Set ℓ} (φ φ₀ φ₁ : CofProp)
  {f₀ : [ φ ∨ φ₀ ] → A} {f₁ : [ φ ∨ φ₁ ] → A}
  → (∀ u → f₀ (∣ inl u ∣) ≡ f₁ (∣ inl u ∣))
  → (∀ v₀ v₁ → f₀ ∣ inr v₀ ∣ ≡ f₁ ∣ inr v₁ ∣)
  → (∀ uv₀ uv₁ → f₀ uv₀ ≡ f₁ uv₁)
takeOutCof φ φ₀ φ₁ {f₀} {f₁} p q =
  ∨-elim φ φ₀ _
    (λ u₀ → ∨-elimEq φ φ₁
      (λ u₁ → trans (p u₁) (cong f₀ (trunc _ _)))
      (λ v₁ → trans (cong f₁ (trunc _ _)) (p u₀)))
    (λ v₀ → ∨-elimEq φ φ₁
      (λ u₁ → trans (p u₁) (cong f₀ (trunc _ _)))
      (λ v₁ → q v₀ v₁))
    (λ _ _ → funext λ _ → uipImp)
