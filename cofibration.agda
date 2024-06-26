{-

Basic operations on and properties of cofibrations.

-}
module cofibration where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape

open import axiom.cofibration public

infix 1 _[_↦_]
infixl 3 _▷[_]
infixr 4 _∨ˣ_

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

------------------------------------------------------------------------------------------
-- Abbreviations.
------------------------------------------------------------------------------------------

--↓ Cofibration for the boundary of the interval shape.

∂ : 𝕀 → Cof
∂ i = 𝕚 ∋ i ≈ 0 ∨ 𝕚 ∋ i ≈ 1

--↓ Context extension by a cofibration.

_▷[_] : (Γ : Type ℓ) (φ : Γ → Cof) → Type ℓ
Γ ▷[ φ ] = Σ γ ∈ Γ , [ φ γ ]

--↓ Restriction along a cofibration.

_↾_ : {A : Γ → Type ℓ} (a : Γ ⊢ˣ A) (φ : Γ → Cof) → Γ ▷[ φ ] ⊢ˣ A ∘ 𝒑
(a ↾ φ) = a ∘ 𝒑

--↓ Operations on cofibrations in context.

[_]ˣ : (Γ → Cof) → (Γ → Type)
[ φ ]ˣ γ = [ φ γ ]

_∋_≈ˣ_ : (S : Shape) → (Γ → ⟨ S ⟩) → (Γ → ⟨ S ⟩) → (Γ → Cof)
(S ∋ r ≈ˣ s) γ = S ∋ r γ ≈ s γ

_∨ˣ_ : (φ ψ : Γ → Cof) → (Γ → Cof)
(φ ∨ˣ ψ) γ = φ γ ∨ ψ γ

--↓ Version of cofIsStrictProp with implicit arguments.

cofIsStrictProp' : (φ : Cof) {u v : [ φ ]} → u ≡ v
cofIsStrictProp' φ = cofIsStrictProp φ _ _

------------------------------------------------------------------------------------------
-- Partial elements.
------------------------------------------------------------------------------------------

--↓ Type of partial elements in a type, that is elements defined when some cofibration
--↓ holds.

_⁺ : Type ℓ → Type ℓ
A ⁺ = Σ φ ∈ Cof , ([ φ ] → A)

------------------------------------------------------------------------------------------
-- Restricted types.
------------------------------------------------------------------------------------------

--↓ A [ φ ↦ a ] is the type of elements of A which are equal to a whenever [ φ ] holds.

record _[_↦_] (A : Type ℓ) (φ : Cof) (a : [ φ ] → A) : Type ℓ where
  constructor makeRestrict
  field
    out : A
    out≡ : ∀ u → a u ≡ out

open _[_↦_] public

--↓ Applying a function to a restricted type.

mapRestrict : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {φ : Cof} {a : [ φ ] → A}
  → A [ φ ↦ a ] → B [ φ ↦ f ∘ a ]
mapRestrict f z .out = f (z .out)
mapRestrict f z .out≡ u = cong f (z .out≡ u)

--↓ Extensionality principle for restricted types.

restrictExt : {A : Type ℓ} {φ : Cof} {a : [ φ ] → A}
  {z z' : A [ φ ↦ a ]}
  → z .out ≡ z' .out
  → z ≡ z'
restrictExt refl = cong (makeRestrict _) (funExt' uip')

--↓ Forget part of a restriction.

narrow : {φ ψ : Cof} {A : Type ℓ} {a : [ φ ] → A}
  → A [ φ ↦ a ] → (f : [ ψ ] → [ φ ]) → A [ ψ ↦ a ∘ f ]
narrow b f .out = b .out
narrow b f .out≡ u = b .out≡ (f u)

------------------------------------------------------------------------------------------
-- Combining compatible partial functions.
------------------------------------------------------------------------------------------

--↓ Derived non-dependent elimination principle for a union of cofibrations.

∨-rec : {φ ψ : Cof} {A : Type ℓ}
  (f : [ φ ] → A)
  (g : [ ψ ] → A)
  (p : ∀ u v → f u ≡ g v)
  → [ φ ∨ ψ ] → A
∨-rec f g p =
  ∨-elim f g (λ u v → substConst _ _ ∙ p u v)

--↓ Functoriality of union of cofibrations.

_∨`_ : {φ ψ φ' ψ' : Cof}
  (f : [ φ ] → [ φ' ])
  (g : [ ψ ] → [ ψ' ])
  → [ φ ∨ ψ ] → [ φ' ∨ ψ' ]
f ∨` g =
  ∨-rec (∨l ∘ f) (∨r ∘ g) (λ _ _ → cofIsStrictProp' (_ ∨ _))

--↓ Derived dependent elimination principle for a union of cofibrations into a family of
--↓ equalities.

opaque
  ∨-elimEq : {φ ψ : Cof} {A : [ φ ∨ ψ ] → Type ℓ}
    {f g : (uv : [ φ ∨ ψ ]) → A uv}
    → ((u : [ φ ]) → f (∨l u) ≡ g (∨l u))
    → ((v : [ ψ ]) → f (∨r v) ≡ g (∨r v))
    → (w : [ φ ∨ ψ ]) → f w ≡ g w
  ∨-elimEq f g =
    ∨-elim f g (λ _ _ → uip')

--↓ Non-dependent and dependent elimination principles for the interval boundary
--↓ cofibration.

∂-rec : (r : 𝕀) {A : Type ℓ}
  → ([ 𝕚 ∋ r ≈ 0 ] → A) → ([ 𝕚 ∋ r ≈ 1 ] → A) → [ ∂ r ] → A
∂-rec r f g =
  ∨-rec f g (λ u v → 0≠1 (sym u ∙ v))

∂-elim : (r : 𝕀) {A : [ ∂ r ] → Type ℓ}
  → ((rO : [ 𝕚 ∋ r ≈ 0 ]) → A (∨l rO))
  → ((rI : [ 𝕚 ∋ r ≈ 1 ]) → A (∨r rI))
  → (r∂ : [ ∂ r ]) → A r∂
∂-elim r f g =
  ∨-elim f g (λ u v → 0≠1 (sym u ∙ v))

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
    ∨-elim
      (λ u₀ → ∨-elimEq
        (λ u₁ → cong f₀ (cofIsStrictProp' (φ ∨ φ₀)) ∙ p u₁)
        (λ v₁ → p u₀ ∙ cong f₁ (cofIsStrictProp' (φ ∨ φ₁))))
      (λ v₀ → ∨-elimEq
        (λ u₁ → cong f₀ (cofIsStrictProp' (φ ∨ φ₀)) ∙ p u₁)
        (λ v₁ → q v₀ v₁))
      (λ _ _ → funExt' uip')

--↓ Substitution for inhabitants of a cofibration.

substCofEl : (φ : Cof) {P : [ φ ] → Type ℓ} {u : [ φ ]} → P u → ∀ v → P v
substCofEl φ {P} p v = subst P (cofIsStrictProp' φ) p

--↓ To check a property indexed by two elements of a cofibration, it suffices to check
--↓ the diagonal.

diagonalCofElim : (φ : Cof) {P : [ φ ] → [ φ ] → Type ℓ}
  → (∀ u → P u u) → (∀ u v → P u v)
diagonalCofElim φ f = substCofEl φ ∘ f
