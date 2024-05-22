{-

Axiomatization of shapes. Postulates a type of shapes, types of homomorphisms between
shapes, and the interval shape.

-}
module axiom.shape where

open import basic
open import axiom.funext

private variable ℓ : Level

infixl 3 _▷⟨_⟩ _^_

------------------------------------------------------------------------------------------
-- Shapes.
------------------------------------------------------------------------------------------

postulate
  --↓ We postulate a universe of shapes.
  --↓ For the equivariant model in cartesian cubical sets, we take Shape to be ℕ and
  --↓ ⟨ n ⟩ to be the n-cube 𝕀ⁿ.

  Shape : Type
  ⟨_⟩ : Shape → Type

  --↓ We postulate a type of homomorphisms between each pair of shapes.
  --↓ For the equivariant model in cartesian cubical sets, the shape homomorphisms are the
  --↓ automorphisms of cubes.

  --↓ For the formalization we do not need that the shape morphisms are closed under
  --↓ composition and identities, but closing under these does not affect the
  --↓ construction. We also do not need that shape morphisms are isomorphisms as in the
  --↓ case of the equivariant model structure on cartesian cubes, but they are constrained
  --↓ to be isomorphism-like by the axioms on cofibrations.

  Shape[_,_] : Shape → Shape → Type
  ⟪_⟫ : {I J : Shape} → Shape[ I , J ] → ⟨ I ⟩ → ⟨ J ⟩

  --↓ Interval shape.
  --↓ The interval shape is used to define path types and thus equivalences and anything
  --↓ that depends on equivalences.

  --↓ In the equivariant model in cartesian cubical sets, this is the shape encoding the
  --↓ 1-cube. In that case every shape is a power of the interval, but the construction
  --↓ does not require that the shapes are generated in this way (nor that shapes are
  --↓ closed under products).

  𝕚 : Shape

--↓ Notation for the interval type.

𝕀 : Type
𝕀 = ⟨ 𝕚 ⟩

postulate
  --↓ We postulate that the interval has two distinct elements (the *endpoints*).

  𝕚0 : 𝕀
  𝕚1 : 𝕀
  0≠1 : {A : Type ℓ} → 𝕚0 ≡ 𝕚1 → A

--↓ Notation for context extension by a shape.

_▷⟨_⟩ : ∀ {ℓ} → Type ℓ → Shape → Type ℓ
Γ ▷⟨ S ⟩ = Γ × ⟨ S ⟩

--↓ Notation for context extension by a copy of the interval.

_▷𝕀 : ∀ {ℓ} → Type ℓ → Type ℓ
Γ ▷𝕀 = Γ ▷⟨ 𝕚 ⟩

postulate
  --↓ We postulate that the type of shapes and the type of homomorphisms between any two
  --↓ shapes are flat-modal, i.e. "discrete".

  --↓ In the motivating cartesian cubical set semantics, this means they are discrete
  --↓ cubical sets, which is indeed the case for the equivariant model: the type of shapes
  --↓ is the *set* ℕ and Shape[ m , n ] is the *set* of automorphisms from the m-cube to the
  --↓ n-cube.

  ShapeIsDiscrete : {A : Shape → Type ℓ}
    → ((@♭ S : Shape) → A S) → ((S : Shape) → A S)

  ShapeIsDiscrete-β : {A : Shape → Type ℓ} (f : (@♭ S : Shape) → A S)
    (@♭ S : Shape) → ShapeIsDiscrete f S ≡ f S

  {-# REWRITE ShapeIsDiscrete-β #-}

  ShapeHomIsDiscrete : {@♭ S T : Shape} {A : Shape[ S , T ] → Type ℓ}
    → ((@♭ σ : Shape[ S , T ]) → A σ) → ((σ : Shape[ S , T ]) → A σ)

  ShapeHomIsDiscrete-β : {@♭ S T : Shape} {A : Shape[ S , T ] → Type ℓ}
    (f : (@♭ σ : Shape[ S , T ]) → A σ)
    (@♭ σ : Shape[ S , T ]) → ShapeHomIsDiscrete f σ ≡ f σ

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

^-unit : ∀ {ℓ} (S : Shape) {Γ : Type ℓ} → Γ → Γ ▷⟨ S ⟩ ^ S
^-unit S = curry id

^-counit : ∀ {ℓ} (S : Shape) {Γ : Type ℓ} → Γ ^ S ▷⟨ S ⟩ → Γ
^-counit S = uncurry _$_

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
