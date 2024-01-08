{-

Postulates a type of shapes, types of homomorphisms between shapes,
and the interval shape

-}
module axiom.shape where

open import basic
open import axiom.funext

private variable ℓ : Level

infixl 3 _▷⟨_⟩ _^_

------------------------------------------------------------------------------------------
-- Shapes
------------------------------------------------------------------------------------------

postulate
  Shape : Type
  ShapeHom : Shape → Shape → Type

  ⟨_⟩ : Shape → Type
  ⟪_⟫ : {I J : Shape} → ShapeHom I J → ⟨ I ⟩ → ⟨ J ⟩

  𝕚 : Shape -- interval shape

𝕀 = ⟨ 𝕚 ⟩

postulate -- interval endpoints
  𝕚0 : 𝕀
  𝕚1 : 𝕀
  0≠1 : {A : Type ℓ} → 𝕚0 ≡ 𝕚1 → A

-- Notation for context extension by a shape
_▷⟨_⟩ : ∀ {ℓ} → Type ℓ → Shape → Type ℓ
Γ ▷⟨ S ⟩ = Γ × ⟨ S ⟩

-- Notation for context extension by the interval
_▷𝕀 : ∀ {ℓ} → Type ℓ → Type ℓ
Γ ▷𝕀 = Γ ▷⟨ 𝕚 ⟩

------------------------------------------------------------------------------------------
-- The objects of shapes and shape morphisms are discrete (i.e., crisp).
------------------------------------------------------------------------------------------

postulate
  ShapeIsDiscrete : {A : Shape → Type ℓ}
    → ((@♭ S : Shape) → A S) → ((S : Shape) → A S)

  ShapeIsDiscrete-β : {A : Shape → Type ℓ} (f : (@♭ S : Shape) → A S)
    (@♭ S : Shape) → ShapeIsDiscrete f S ≡ f S

  {-# REWRITE ShapeIsDiscrete-β #-}

  ShapeHomIsDiscrete : {@♭ S T : Shape} {A : ShapeHom S T → Type ℓ}
    → ((@♭ σ : ShapeHom S T) → A σ) → ((σ : ShapeHom S T) → A σ)

  ShapeHomIsDiscrete-β : {@♭ S T : Shape} {A : ShapeHom S T → Type ℓ}
    (f : (@♭ σ : ShapeHom S T) → A σ)
    (@♭ σ : ShapeHom S T) → ShapeHomIsDiscrete f σ ≡ f σ

  {-# REWRITE ShapeHomIsDiscrete-β #-}

------------------------------------------------------------------------------------------
-- Convenient notation for exponentiation by a shape.
------------------------------------------------------------------------------------------

--↓ Exponentiation by a shape.

_^_ : ∀ {ℓ} (Γ : Type ℓ) (S : Shape) → Type ℓ
Γ ^ S = ⟨ S ⟩ → Γ

--↓ Functorial action of exponentiation by a shape.

_`^_ : ∀ {ℓ ℓ'} {Γ : Type ℓ} {Γ' : Type ℓ'}
  (ρ : Γ → Γ') (S : Shape) → (Γ ^ S → Γ' ^ S)
(ρ `^ S) = ρ ∘_

--↓ Unit and counit transformations for the adjunction between product with (_▷ S) and
--↓ exponentation by (_^ S) a shape.

^-η : ∀ {ℓ} (S : Shape) {Γ : Type ℓ} → Γ → Γ ▷⟨ S ⟩ ^ S
^-η S = curry id

^-ε : ∀ {ℓ} (S : Shape) {Γ : Type ℓ} → Γ ^ S ▷⟨ S ⟩ → Γ
^-ε S = uncurry _$_

------------------------------------------------------------------------------------------
-- Notation for interval endpoints.
-- Using Agda's support for natural number literal overloading, we can write 0 and 1 for
-- the endpoints of the interval shape.
------------------------------------------------------------------------------------------

private
  isEndpoint : (m : ℕ) → Type
  isEndpoint 0 = 𝟙
  isEndpoint 1 = 𝟙
  isEndpoint (suc (suc _)) = 𝟘

  𝕀fromℕ : (n : ℕ) → {{_ : isEndpoint n}} → 𝕀
  𝕀fromℕ 0 = 𝕚0
  𝕀fromℕ 1 = 𝕚1

instance
  Num𝕀 : Number 𝕀
  Num𝕀 .Number.Constraint = isEndpoint
  Num𝕀 .Number.fromNat = 𝕀fromℕ
