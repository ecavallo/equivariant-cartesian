{-

Summary of the fibrant model.

-}
module summary where

open import basic
open import internal-extensional-type-theory
import fibration.fibration
import type-former.empty
import type-former.natural-number
import type-former.path
import type-former.pi
import type-former.sigma
import type-former.swan-identity
import type-former.unit
import universe

infix 1 _⊢ᶠType_ _⊢ᶠ_
infixl 3 _▷ᶠ_
infixr 5 _∘ᶠ_ _∘ᵗᵐ_

open fibration.fibration using (_$ᶠ_)

private variable
  ℓ ℓ' : Level
  Δ Γ : Type ℓ

------------------------------------------------------------------------------------------
-- Judgments of the fibrant type theory.
------------------------------------------------------------------------------------------

--↓ A context is a type of the ambient theory.

Ctx : ∀ ℓ → Type (lsuc ℓ)
Ctx ℓ = Type ℓ

--↓ A type over Γ is a type family over Γ in the ambient theory equipped with a /fibration
--↓ structure/.

_⊢ᶠType_ : (Γ : Ctx ℓ) (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Γ ⊢ᶠType ℓ' = fibration.fibration._⊢ᶠType_ Γ ℓ'

--↓ A term of a type is a section of the type family.

_⊢ᶠ_ : (Γ : Ctx ℓ) (A : Γ ⊢ᶠType ℓ') → Type (ℓ ⊔ ℓ')
Γ ⊢ᶠ A = fibration.fibration._⊢ᶠ_ Γ A

--↓ Equality of types and terms is equality in the ambient theory.

_⊢ᶠ_≡_⦂Type : (Γ : Ctx ℓ) (A₀ A₁ : Γ ⊢ᶠType ℓ') → Type (ℓ ⊔ lsuc ℓ')
Γ ⊢ᶠ A₀ ≡ A₁ ⦂Type = A₀ ≡ A₁

infix 1 _⊢ᶠ_≡_⦂Type

EqTerm : (Γ : Ctx ℓ) (A : Γ ⊢ᶠType ℓ') (a₀ a₁ : Γ ⊢ᶠ A) → Type (ℓ ⊔ ℓ')
EqTerm Γ A a₀ a₁ = a₀ ≡ a₁

infix 1 EqTerm
syntax EqTerm Γ A a₀ a₁ = Γ ⊢ᶠ a₀ ≡ a₁ ⦂ A

------------------------------------------------------------------------------------------
-- Contexts.
------------------------------------------------------------------------------------------

--↓ Terminal context.

⋄ : Ctx lzero
⋄ = 𝟙

--↓ Context extension.

_▷ᶠ_ : (Γ : Ctx ℓ) (A : Γ ⊢ᶠType ℓ') → Ctx (ℓ ⊔ ℓ')
Γ ▷ᶠ A = fibration.fibration._▷ᶠ_ Γ A

--↓ Substitution for types.

_∘ᶠ_ : (A : Γ ⊢ᶠType ℓ) (σ : Δ → Γ) → Δ ⊢ᶠType ℓ
A ∘ᶠ ρ = fibration.fibration._∘ᶠ_ A ρ

--↓ Substitution for terms is interpreted as ordinary function composition.

_∘ᵗᵐ_ : {A : Γ ⊢ᶠType ℓ} (a : Γ ⊢ᶠ A) (ρ : Δ → Γ) → Δ ⊢ᶠ (A ∘ᶠ ρ)
a ∘ᵗᵐ ρ = a ∘ ρ

------------------------------------------------------------------------------------------
-- Empty type.
------------------------------------------------------------------------------------------

--↓ Formation.

𝟘ᶠ : Γ ⊢ᶠType lzero
𝟘ᶠ = type-former.empty.𝟘ᶠ

--↓ Elimination.

𝟘-elimᶠ :
  (A : Γ ▷ᶠ 𝟘ᶠ ⊢ᶠType ℓ)
  (c : Γ ⊢ᶠ 𝟘ᶠ)
  → Γ ⊢ᶠ A ∘ᶠ (id ,, c)
𝟘-elimᶠ A c γ = 𝟘-rec (c γ)

------------------------------------------------------------------------------------------
-- Natural number type.
------------------------------------------------------------------------------------------

--↓ Formation.

ℕᶠ : Γ ⊢ᶠType lzero
ℕᶠ = type-former.natural-number.ℕᶠ

--↓ Introduction.

zeroᶠ : Γ ⊢ᶠ ℕᶠ
zeroᶠ = type-former.natural-number.zeroᶠ

sucᶠ :
  (n : Γ ⊢ᶠ ℕᶠ)
  → Γ ⊢ᶠ ℕᶠ
sucᶠ = type-former.natural-number.sucᶠ

--↓ Elimination.

ℕ-elimᶠ :
  (P : Γ ▷ᶠ ℕᶠ ⊢ᶠType ℓ)
  (z : Γ ⊢ᶠ P ∘ᶠ (id ,, zeroᶠ))
  (s : Γ ▷ᶠ ℕᶠ ▷ᶠ P ⊢ᶠ P ∘ᶠ (𝒑 ∘ 𝒑 ,, sucᶠ (𝒒 ∘ 𝒑)))
  (n : Γ ⊢ᶠ ℕᶠ)
  → Γ ⊢ᶠ P ∘ᶠ (id ,, n)
ℕ-elimᶠ = type-former.natural-number.ℕ-elimᶠ

ℕ-elim-zeroᶠ :
  (P : Γ ▷ᶠ ℕᶠ ⊢ᶠType ℓ)
  (z : Γ ⊢ᶠ P ∘ᶠ (id ,, zeroᶠ))
  (s : Γ ▷ᶠ ℕᶠ ▷ᶠ P ⊢ᶠ P ∘ᶠ (𝒑 ∘ 𝒑 ,, sucᶠ (𝒒 ∘ 𝒑)))
  → Γ ⊢ᶠ ℕ-elimᶠ P z s zeroᶠ ≡ z ⦂ P ∘ᶠ (id ,, zeroᶠ)
ℕ-elim-zeroᶠ _ _ _ = refl

ℕ-elim-sucᶠ :
  (P : Γ ▷ᶠ ℕᶠ ⊢ᶠType ℓ)
  (z : Γ ⊢ᶠ P ∘ᶠ (id ,, zeroᶠ))
  (s : Γ ▷ᶠ ℕᶠ ▷ᶠ P ⊢ᶠ P ∘ᶠ (𝒑 ∘ 𝒑 ,, sucᶠ (𝒒 ∘ 𝒑)))
  (n : Γ ⊢ᶠ ℕᶠ)
  → Γ ⊢ᶠ ℕ-elimᶠ P z s (sucᶠ n) ≡ s ∘ (id ,, n ,, ℕ-elimᶠ P z s n) ⦂ P ∘ᶠ (id ,, sucᶠ n)
ℕ-elim-sucᶠ _ _ _ _ = refl

------------------------------------------------------------------------------------------
-- Π-type
------------------------------------------------------------------------------------------

Πᶠ :
  (A : Γ ⊢ᶠType ℓ)
  (B : Γ ▷ᶠ A ⊢ᶠType ℓ')
  → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Πᶠ = type-former.pi.Πᶠ

module _ (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ') where

  --↓ Introduction.

  λᶠ :
    Γ ▷ᶠ A ⊢ᶠ B
    → Γ ⊢ᶠ Πᶠ A B
  λᶠ = type-former.pi.λˣ

  --↓ Elimination.

  appᶠ :
    (f : Γ ⊢ᶠ Πᶠ A B)
    (a : Γ ⊢ᶠ A)
    → Γ ⊢ᶠ B ∘ᶠ (id ,, a)
  appᶠ = type-former.pi.appˣ

  --↓ Computation.

  app-λᶠ :
    (b : Γ ▷ᶠ A ⊢ᶠ B)
    (a : Γ ⊢ᶠ A)
    → Γ ⊢ᶠ appᶠ (λᶠ b) a ≡ b ∘ (id ,, a) ⦂ B ∘ᶠ (id ,, a)
  app-λᶠ _ _ = refl

--↓ Uniqueness.

Π-ηᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ')
  (f : Γ ⊢ᶠ Πᶠ A B)
  → Γ ⊢ᶠ f ≡ λᶠ A B (appᶠ (A ∘ᶠ 𝒑) (B ∘ᶠ (𝒑 ∘ 𝒑 ,, 𝒒)) (f ∘ 𝒑) 𝒒) ⦂ Πᶠ A B
Π-ηᶠ _ _ _ = refl

------------------------------------------------------------------------------------------
-- Σ-type.
------------------------------------------------------------------------------------------

--↓ Formation.

Σᶠ :
  (A : Γ ⊢ᶠType ℓ)
  (B : Γ ▷ᶠ A ⊢ᶠType ℓ')
  → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Σᶠ = type-former.sigma.Σᶠ

module _ (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ') where

  --↓ Introduction.

  pairᶠ :
    (a : Γ ⊢ᶠ A)
    (b : Γ ⊢ᶠ B ∘ᶠ (id ,, a))
    → Γ ⊢ᶠ Σᶠ A B
  pairᶠ = type-former.sigma.pairᶠ A B

  --↓ Elimination.

  fstᶠ :
    Γ ⊢ᶠ Σᶠ A B
    → Γ ⊢ᶠ A
  fstᶠ = type-former.sigma.fstˣ

  sndᶠ :
    (t : Γ ⊢ᶠ Σᶠ A B)
    → Γ ⊢ᶠ B ∘ᶠ (id ,, fstᶠ t)
  sndᶠ = type-former.sigma.sndˣ

  --↓ Uniqueness (η-principle).

  Σ-ηᶠ :
    (t : Γ ⊢ᶠ Σᶠ A B)
    → Γ ⊢ᶠ t ≡ pairᶠ (fstᶠ t) (sndᶠ t) ⦂ Σᶠ A B
  Σ-ηᶠ t = refl

------------------------------------------------------------------------------------------
-- Weak identity ("path") type.
------------------------------------------------------------------------------------------

--↓ Formation.

Pathᶠ :
  (A : Γ ⊢ᶠType ℓ)
  (a₀ a₁ : Γ ⊢ᶠ A)
  → Γ ⊢ᶠType ℓ
Pathᶠ = type-former.path.Pathᶠ

--↓ Introduction.

reflᶠ :
  (A : Γ ⊢ᶠType ℓ)
  (a : Γ ⊢ᶠ A)
  → Γ ⊢ᶠ Pathᶠ A a a
reflᶠ = type-former.path.reflᶠ

--↓ Elimination.
--↓ We state a Paulin-Mohring-style J rule using the type of singletons.

Singlᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
Singlᶠ A a = Σᶠ A (Pathᶠ (A ∘ᶠ 𝒑) 𝒒 (a ∘ 𝒑))

singlCenterᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  → Γ ⊢ᶠ Singlᶠ A a
singlCenterᶠ A a =
  pairᶠ A (Pathᶠ (A ∘ᶠ 𝒑) 𝒒 (a ∘ 𝒑)) a (reflᶠ A a)

Jᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
  (P : Γ ▷ᶠ Singlᶠ A a ⊢ᶠType ℓ')
  (d : Γ ⊢ᶠ P ∘ᶠ (id ,, singlCenterᶠ A a))
  (c : Γ ⊢ᶠ Singlᶠ A a)
  → Γ ⊢ᶠ P ∘ᶠ (id ,, c)
Jᶠ = type-former.path.Jᶠ

------------------------------------------------------------------------------------------
-- Unit type.
------------------------------------------------------------------------------------------

--↓ Formation.

𝟙ᶠ : Γ ⊢ᶠType lzero
𝟙ᶠ = type-former.unit.𝟙ᶠ

--↓ Introduction.

∗ᶠ : Γ ⊢ᶠ 𝟙ᶠ
∗ᶠ _ = _

--↓ Uniqueness (η-principle).

∗-ηᶠ :
  (t : Γ ⊢ᶠ 𝟙ᶠ)
  → Γ ⊢ᶠ ∗ᶠ ≡ t ⦂ 𝟙ᶠ
∗-ηᶠ _ = refl

------------------------------------------------------------------------------------------
-- Universes.
------------------------------------------------------------------------------------------

--↓ Formation.

𝑼ᶠ : (@♭ ℓ : Level)
  → Γ ⊢ᶠType (lsuc ℓ)
𝑼ᶠ = universe.𝑼ᶠ

--↓ Decoding elements of the universe to types.

Elᶠ : {@♭ ℓ : Level}
  → Γ ⊢ᶠ 𝑼ᶠ ℓ
  → Γ ⊢ᶠType ℓ
Elᶠ = universe.Elᶠ

------------------------------------------------------------------------------------------
-- Closure of universes under type formers.
------------------------------------------------------------------------------------------

--↓ Empty type.

𝟘ᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
𝟘ᵁᶠ = universe.𝟘ᵁᶠ

El-𝟘ᶠ : Γ ⊢ᶠ Elᶠ 𝟘ᵁᶠ ≡ 𝟘ᶠ ⦂Type
El-𝟘ᶠ = universe.El-𝟘ᶠ

--↓ Unit type.

𝟙ᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
𝟙ᵁᶠ = universe.𝟙ᵁᶠ

El-𝟙ᶠ : Γ ⊢ᶠ Elᶠ 𝟙ᵁᶠ ≡ 𝟙ᶠ ⦂Type
El-𝟙ᶠ = universe.El-𝟙ᶠ

--↓ Natural number type.

ℕᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
ℕᵁᶠ = universe.ℕᵁᶠ

El-ℕᶠ : Γ ⊢ᶠ Elᶠ ℕᵁᶠ ≡ ℕᶠ ⦂Type
El-ℕᶠ = universe.El-ℕᶠ

module _ {@♭ ℓ : Level} where

  --↓ Σ-type.

  Σᵁᶠ :
    (A : Γ ⊢ᶠ 𝑼ᶠ ℓ)
    (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
    → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Σᵁᶠ = universe.Σᵁᶠ

  El-Σᶠ :
    (A : Γ ⊢ᶠ 𝑼ᶠ ℓ)
    (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
    → Γ ⊢ᶠ Elᶠ (Σᵁᶠ A B) ≡ Σᶠ (Elᶠ A) (Elᶠ B) ⦂Type
  El-Σᶠ = universe.El-Σᶠ

  --↓ Π-type.

  Πᵁᶠ :
    (A : Γ ⊢ᶠ 𝑼ᶠ ℓ)
    (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
    → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Πᵁᶠ = universe.Πᵁᶠ

  El-Πᶠ :
    (A : Γ ⊢ᶠ 𝑼ᶠ ℓ)
    (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
    → Γ ⊢ᶠ Elᶠ (Πᵁᶠ A B) ≡ Πᶠ (Elᶠ A) (Elᶠ B) ⦂Type
  El-Πᶠ = universe.El-Πᶠ

  --↓ Weak identity type.

  Pathᵁᶠ :
    (A : Γ ⊢ᶠ 𝑼ᶠ ℓ)
    (a₀ a₁ : Γ ⊢ᶠ Elᶠ A)
    → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Pathᵁᶠ = universe.Pathᵁᶠ

  El-Pathᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A)
    → Γ ⊢ᶠ Elᶠ (Pathᵁᶠ A a₀ a₁) ≡ Pathᶠ (Elᶠ A) a₀ a₁ ⦂Type
  El-Pathᶠ = universe.El-Pathᶠ

------------------------------------------------------------------------------------------
-- Univalence axiom.
------------------------------------------------------------------------------------------

module _ (@♭ ℓ : Level) where

  --↓ The univalence axiom, stated as contractibility of (Σ B:𝑼. B ≃ A) for all A : 𝑼.
  --↓ See the referenced modules below for definitions of the derived type formers ≃ᶠ (the
  --↓ type of equivalences) and IsContrᶠ (the type of proofs of contractibility). Both are
  --↓ defined using the weak identity type Pathᶠ introduced above.

  open import type-former.equiv using (_≃ᶠ_)
  open import type-former.hlevels using (IsContrᶠ)

  UA : ⋄ ⊢ᶠ Πᶠ (𝑼ᶠ ℓ) (IsContrᶠ (Σᶠ (𝑼ᶠ ℓ) (Elᶠ 𝒒 ≃ᶠ Elᶠ (𝒒 ∘ 𝒑))))
  UA = universe.UA ℓ

------------------------------------------------------------------------------------------
-- Strict identity type à la Swan.
--
-- This construction uses two additional axioms not postulated in the axiom modules,
-- namely cofibration extensionality and closure of the universe of cofibrations under
-- Σ-types.
------------------------------------------------------------------------------------------

module _
  (@♭ ext : type-former.swan-identity.CofExtensionality)
  (@♭ dom : type-former.swan-identity.CofHasΣ)
  where

  module swan = type-former.swan-identity.SwanIdentity ext dom

  --↓ Formation.

  Idᶠ :
    (A : Γ ⊢ᶠType ℓ)
    (a₀ a₁ : Γ ⊢ᶠ A)
    → Γ ⊢ᶠType ℓ
  Idᶠ = swan.Idᶠ

  --↓ Introduction.

  idreflᶠ :
    (A : Γ ⊢ᶠType ℓ)
    (a : Γ ⊢ᶠ A)
    → Γ ⊢ᶠ Idᶠ A a a
  idreflᶠ = swan.idreflᶠ

  --↓ Elimination in terms of the singleton type.

  IdSinglᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A) → Γ ⊢ᶠType ℓ
  IdSinglᶠ A a =
    Σᶠ A (Idᶠ (A ∘ᶠ 𝒑) 𝒒 (a ∘ 𝒑))

  idSinglCenterᶠ : (A : Γ ⊢ᶠType ℓ) (a : Γ ⊢ᶠ A)
    → Γ ⊢ᶠ IdSinglᶠ A a
  idSinglCenterᶠ A a =
    pairᶠ A (Idᶠ (A ∘ᶠ 𝒑) 𝒒 (a ∘ 𝒑)) a (idreflᶠ A a)

  idJᶠ :
    (A : Γ ⊢ᶠType ℓ)
    (a : Γ ⊢ᶠ A)
    (P : Γ ▷ᶠ IdSinglᶠ A a ⊢ᶠType ℓ')
    (d : Γ ⊢ᶠ P ∘ᶠ (id ,, idSinglCenterᶠ A a))
    (c : Γ ⊢ᶠ IdSinglᶠ A a)
    → Γ ⊢ᶠ P ∘ᶠ (id ,, c)
  idJᶠ = swan.idJᶠ

  --↓ Strict computation rule for identity elimination applied at reflexivity.

  idJreflᶠ :
    (A : Γ ⊢ᶠType ℓ)
    (a : Γ ⊢ᶠ A)
    (P : Γ ▷ᶠ IdSinglᶠ A a ⊢ᶠType ℓ')
    (d : Γ ⊢ᶠ P ∘ᶠ (id ,, idSinglCenterᶠ A a))
    → Γ ⊢ᶠ idJᶠ A a P d (idSinglCenterᶠ A a) ≡ d ⦂ P ∘ᶠ (id ,, idSinglCenterᶠ A a)
  idJreflᶠ A a P d = swan.idJreflᶠ A a P d

  --↓ Closure of the universe under strict identity types.

  module _ {@♭ ℓ : Level} where

    module swanᵁ = universe.SwanIdentityᵁ {ℓ} ext dom

    Idᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A) → Γ ⊢ᶠ 𝑼ᶠ ℓ
    Idᵁᶠ = swanᵁ.Idᵁᶠ

    El-Idᶠ :
      (A : Γ ⊢ᶠ 𝑼ᶠ ℓ)
      (a₀ a₁ : Γ ⊢ᶠ Elᶠ A)
      → Γ ⊢ᶠ Elᶠ (Idᵁᶠ A a₀ a₁) ≡ Idᶠ (Elᶠ A) a₀ a₁ ⦂Type
    El-Idᶠ = swanᵁ.El-Idᶠ
