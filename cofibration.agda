{-

Basic properties of cofibrations

-}
module cofibration where

open import prelude
open import axiom.funext
open import axiom.truncation
open import axiom.shape

open import axiom.cofibration public

infixr 4 _∨ᴵ_

private variable
  ℓ ℓ' : Level
  Γ : Type ℓ

------------------------------------------------------------------------------------------
-- Abbreviations
------------------------------------------------------------------------------------------

--↓ Cofibration for the boundary of the interval shape.

∂ : 𝕀 → Cof
∂ i = 𝕚 ∋ i ≈ 0 ∨ 𝕚 ∋ i ≈ 1

--↓ Coprojections into union of cofibrations.

∨l : {A : Type ℓ} {B : Type ℓ'} → A → ∥ A ⊎ B ∥
∨l a = ∣ inl a ∣

∨r : {A : Type ℓ} {B : Type ℓ'} → B → ∥ A ⊎ B ∥
∨r b = ∣ inr b ∣

--↓ Implication between cofibrations.

_⇒_ : Cof → Cof → Type
φ ⇒ ψ = [ φ ] → [ ψ ]

--↓ Context extension by a cofibration.

_▷[_] : (Γ : Type ℓ) (φ : Γ → Cof) → Type ℓ
Γ ▷[ φ ] = Σ γ ∈ Γ , [ φ γ ]

wk[_] : (φ : Γ → Cof)
  → Γ ▷[ φ ] → Γ
wk[ φ ] = fst

--↓ Operations on cofibrations in context.

_∋_≈ᴵ_ : (S : Shape) → (Γ → ⟨ S ⟩) → (Γ → ⟨ S ⟩) → (Γ → Cof)
(S ∋ r ≈ᴵ s) γ = S ∋ r γ ≈ s γ

_∨ᴵ_ : (φ ψ : Γ → Cof) → (Γ → Cof)
(φ ∨ᴵ ψ) γ = φ γ ∨ ψ γ

_⇒ᴵ_ : (Γ → Cof) → (Γ → Cof) → (Γ → Type)
(φ ⇒ᴵ ψ) γ = φ γ ⇒ ψ γ

--↓ Version of cofIsProp with implicit arguments.

cofIsProp' : (φ : Cof) {u v : [ φ ]} → u ≡ v
cofIsProp' φ = cofIsProp φ _ _

------------------------------------------------------------------------------------------
-- Restricted types
------------------------------------------------------------------------------------------

--↓ A [ φ ↦ a ] is the type of elements of A which are equal to a whenever [ φ ] is
--↓ inhabited.

record _[_↦_] (A : Type ℓ) (φ : Cof) (a : [ φ ] → A) : Type ℓ where
  constructor makeRestrict
  field
    out : A
    out≡ : ∀ u → a u ≡ out

open _[_↦_] public

--↓ Extensionality principle for restricted types.

restrictExt : {A : Type ℓ} {φ : Cof} {a : [ φ ] → A}
  {z z' : A [ φ ↦ a ]}
  → z .out ≡ z' .out
  → z ≡ z'
restrictExt refl = cong (makeRestrict _) (funExt' uip')

--↓ Forget part of a restriction

narrow : {φ ψ : Cof} {A : Type ℓ} {a : [ φ ] → A}
  → A [ φ ↦ a ] → (f : [ ψ ] → [ φ ]) → A [ ψ ↦ a ∘ f ]
narrow b f .out = b .out
narrow b f .out≡ u = b .out≡ (f u)

------------------------------------------------------------------------------------------
-- Combining compatible partial functions
------------------------------------------------------------------------------------------

--↓ Non-dependent elimination principle for a union of cofibrations.

∨-rec : {A : Type ℓ} (φ ψ : Cof)
  (f : [ φ ] → A)
  (g : [ ψ ] → A)
  (p : ∀ u v → f u ≡ g v)
  → [ φ ∨ ψ ] → A
∨-rec φ ψ f g p = ∥∥-rec _ map eq
  where
  map = [ f ∣ g ]

  opaque
    eq : (a b : [ φ ] ⊎ [ ψ ]) → map a ≡ map b
    eq (inl _) (inl _) = cong f (cofIsProp' φ)
    eq (inl u) (inr v) = p u v
    eq (inr v) (inl u) = sym (p u v)
    eq (inr _) (inr _) = cong g (cofIsProp' ψ)

--↓ Dependent elimination principle for a union of cofibrations.

∨-elim : (φ ψ : Cof) {P : [ φ ∨ ψ ] → Type ℓ}
  (f : (u : [ φ ]) → P (∨l u))
  (g : (v : [ ψ ]) → P (∨r v))
  (p : (u : [ φ ]) (v : [ ψ ]) → subst P trunc' (f u) ≡ g v)
  (w : [ φ ∨ ψ ]) → P w
∨-elim φ ψ {P = P} f g p =  ∥∥-elim _ map eq
  where
  map = [ f ∣ g ]

  opaque
    eq : (a b : [ φ ] ⊎ [ ψ ]) → subst P (trunc ∣ a ∣ ∣ b ∣) (map a) ≡ map b
    eq (inl u) (inl u') =
      cong (subst P ⦅–⦆ (f u)) uip'
      ∙ sym (substCongAssoc P ∨l (cofIsProp φ u u') _)
      ∙ congdep f (cofIsProp φ u u')
    eq (inl u) (inr v) = p u v
    eq (inr v) (inl u) = sym (adjustSubstEq P trunc' refl refl trunc' (p u v))
    eq (inr v) (inr v') =
      cong (subst P ⦅–⦆ (g v)) uip'
      ∙ sym (substCongAssoc P ∨r (cofIsProp ψ v v') _)
      ∙ congdep g (cofIsProp ψ v v')

--↓ Derived dependent elimination principle for a union of cofibrations into a family of
--↓ propositions.

opaque
  ∨-elimProp : (φ ψ : Cof) {P : [ φ ∨ ψ ] → Type ℓ}
    (propP : ∀ uv → isProp (P uv))
    (f : (u : [ φ ]) → P (∨l u))
    (g : (v : [ ψ ]) → P (∨r v))
    (w : [ φ ∨ ψ ]) → P w
  ∨-elimProp φ ψ propP f g =
    ∨-elim φ ψ f g (λ _ _ → propP _ _ _)

--↓ Derived dependent elimination principle for a union of cofibrations into a family of
--↓ equalities

opaque
  ∨-elimEq : (φ ψ : Cof) {A : [ φ ∨ ψ ] → Type ℓ}
    {f g : (uv : [ φ ∨ ψ ]) → A uv}
    → ((u : [ φ ]) → f (∨l u) ≡ g (∨l u))
    → ((v : [ ψ ]) → f (∨r v) ≡ g (∨r v))
    → (w : [ φ ∨ ψ ]) → f w ≡ g w
  ∨-elimEq φ ψ =
    ∨-elimProp φ ψ (λ _ → uip)

--↓ Non-dependent and dependent elimination principles for the interval boundary
--↓ cofibration.

∂-rec : (r : 𝕀) {A : Type ℓ}
  → ([ 𝕚 ∋ r ≈ 0 ] → A) → ([ 𝕚 ∋ r ≈ 1 ] → A) → [ ∂ r ] → A
∂-rec r f g =
  ∨-rec (𝕚 ∋ r ≈ 0) (𝕚 ∋ r ≈ 1) f g (λ u v → 0≠1 (sym u ∙ v))

∂-elim : (r : 𝕀) {A : [ ∂ r ] → Type ℓ}
  → ((rO : [ 𝕚 ∋ r ≈ 0 ]) → A (∨l rO))
  → ((rI : [ 𝕚 ∋ r ≈ 1 ]) → A (∨r rI))
  → (r∂ : [ ∂ r ]) → A r∂
∂-elim r f g =
  ∨-elim (𝕚 ∋ r ≈ 0) (𝕚 ∋ r ≈ 1) f g (λ {refl r≡I → 0≠1 r≡I})

--↓ To check that a map [ φ ∨ φ₀ ] → A and a map [ φ ∨ φ₁ ] → A agree on their
--↓ intersection, it suffices to check that they agree on [ φ ] and on the intersection of
--↓ [ φ₀ ] and [ φ₁ ].

opaque
  takeOutCof : {A : Type ℓ} (φ φ₀ φ₁ : Cof)
    {f₀ : [ φ ∨ φ₀ ] → A} {f₁ : [ φ ∨ φ₁ ] → A}
    → (∀ u → f₀ (∨l u) ≡ f₁ (∨l u))
    → (∀ v₀ v₁ → f₀ (∨r v₀) ≡ f₁ (∨r v₁))
    → (∀ uv₀ uv₁ → f₀ uv₀ ≡ f₁ uv₁)
  takeOutCof φ φ₀ φ₁ {f₀} {f₁} p q =
    ∨-elim φ φ₀
      (λ u₀ → ∨-elimEq φ φ₁
        (λ u₁ → cong f₀ trunc' ∙ p u₁)
        (λ v₁ → p u₀ ∙ cong f₁ trunc'))
      (λ v₀ → ∨-elimEq φ φ₁
        (λ u₁ → cong f₀ trunc' ∙ p u₁)
        (λ v₁ → q v₀ v₁))
      (λ _ _ → funExt' uip')

--↓ Substitution for inhabitants of a cofibration

substCofEl : (φ : Cof) {P : [ φ ] → Type ℓ} {u : [ φ ]} → P u → ∀ v → P v
substCofEl φ {P} p v = subst P (cofIsProp φ _ v) p

--↓ To check a property indexed by two elements of a cofibration, it suffices to check
--↓ the diagonal.

diagonalCofElim : (φ : Cof) {P : [ φ ] → [ φ ] → Type ℓ}
  → (∀ u → P u u) → (∀ u v → P u v)
diagonalCofElim φ f = substCofEl φ ∘ f
