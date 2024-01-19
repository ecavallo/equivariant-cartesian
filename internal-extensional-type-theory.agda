{-

Internal interpretation of extensional type theory.

Each universe Type ℓ of our ambient extensional type theory gives us an /internal/
interpretation of extensional type theory: contexts are elements of Type ℓ and a type over
Γ is a family Γ → Type ℓ.

To build an interpretation of homotopy type theory, where contexts are again interpreted
as types Γ : Type ℓ and types are interpreted as families Γ → Type ℓ equipped with
/fibration structures/, it is convenient to have some suggestive notation for the internal
extensional type theory.

To disambiguate from the interpretation of homotopy type theory when necessary, we use the
superscript ˣ to indicate operators on eXtensional types/terms. Note that we sometimes use
ˣ to mark an operator on extensional types/terms which is however named for its role in
the homotopical interpretation. For example, we write A ≃ˣ B for the underlying
extensional type of the fibrant type of equivalences A ≃ᶠ B (with inverses up to path
equality), even though this is distinct from the standard type of equivalences (i.e., with
inverses up to strict equality) for the extensional type theory.

-}

module internal-extensional-type-theory where

open import basic

private variable
  ℓ ℓ' ℓ'' : Level
  Γ Δ : Type ℓ

infix  1 _⊢ˣ_
infixl 3 _▷ˣ_ _,,_ _,ˣ_
infixr 3 _→ˣ_ _×ˣ_

--↓ Term judgment of the extensional type theory.

_⊢ˣ_ : (Γ : Type ℓ) (A : Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
(Γ ⊢ˣ A) = Π Γ A

--↓ Term equality judgment.

syntax EqTermSyntaxˣ Γ A a₀ a₁ = Γ ⊢ˣ a₀ ≡ a₁ ⦂ A

EqTermSyntaxˣ : (Γ : Type ℓ) (A : Γ → Type ℓ') (a₀ a₁ : Γ ⊢ˣ A) → Type (ℓ ⊔ ℓ')
EqTermSyntaxˣ Γ A a₀ a₁ = a₀ ≡ a₁

infix 1 EqTermSyntaxˣ

--↓ Context and substitution extension for the extensional type theory.

_▷ˣ_ : (Γ : Type ℓ) → (Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
Γ ▷ˣ A = Σ Γ A

_,,_ : {A : Γ → Type ℓ''} (ρ : Δ → Γ) (a : Δ ⊢ˣ A ∘ ρ) → (Δ → Γ ▷ˣ A)
(ρ ,, a) δ .fst = ρ δ
(ρ ,, a) δ .snd = a δ

--↓ Projection substitution from an extended context.
--↓ In Agda's input mode, this is \MIp.

𝒑 : {Γ : Type ℓ} {A : Γ → Type ℓ'} → Γ ▷ˣ A → Γ
𝒑 = fst

--↓ Variable term in an extended context.
--↓ In Agda's input mode, this is \MIq.

𝒒 : {Γ : Type ℓ} {A : Γ → Type ℓ'} → Γ ▷ˣ A ⊢ˣ A ∘ 𝒑
𝒒 = snd

------------------------------------------------------------------------------------------
-- Π-types
------------------------------------------------------------------------------------------

Πˣ : (A : Γ → Type ℓ) (B : Γ ▷ˣ A → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
Πˣ A B γ = (a : A γ) → B (γ , a)

_→ˣ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
A →ˣ B = Πˣ A (B ∘ 𝒑)

λˣ : {A : Γ → Type ℓ} {B : Γ ▷ˣ A → Type ℓ'}
  → Γ ▷ˣ A ⊢ˣ B
  → Γ ⊢ˣ Πˣ A B
λˣ f γ a = f (γ , a)

appˣ : {A : Γ → Type ℓ} {B : Γ ▷ˣ A → Type ℓ'}
  → (f : Γ ⊢ˣ Πˣ A B) (a : Γ ⊢ˣ A)
  → Γ ⊢ˣ B ∘ (id ,, a)
appˣ f a γ = f γ (a γ)

------------------------------------------------------------------------------------------
-- Σ-types
------------------------------------------------------------------------------------------

Σˣ : (A : Γ → Type ℓ) (B : Γ ▷ˣ A → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
Σˣ A B γ = Σ a ∈ A γ , B (γ , a)

_×ˣ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
A ×ˣ B = Σˣ A (B ∘ 𝒑)

_,ˣ_ : {A : Γ → Type ℓ} {B : Γ ▷ˣ A → Type ℓ'}
  (a : Γ ⊢ˣ A) → Γ ⊢ˣ B ∘ (id ,, a) → Γ ⊢ˣ Σˣ A B
(a ,ˣ b) γ .fst = a γ
(a ,ˣ b) γ .snd = b γ

fstˣ : {A : Γ → Type ℓ} {B : Γ ▷ˣ A → Type ℓ'}
  → Γ ⊢ˣ Σˣ A B → Γ ⊢ˣ A
fstˣ = fst ∘_

sndˣ : {A : Γ → Type ℓ} {B : Γ ▷ˣ A → Type ℓ'}
  (t : Γ ⊢ˣ Σˣ A B) → Γ ⊢ˣ B ∘ (id ,, fstˣ t)
sndˣ = snd ∘_

------------------------------------------------------------------------------------------
-- Isomorphisms
------------------------------------------------------------------------------------------

_≅ˣ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
_≅ˣ_ A B γ = A γ ≅ B γ

------------------------------------------------------------------------------------------
-- Binary coproducts
------------------------------------------------------------------------------------------

_⊎ˣ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
(A ⊎ˣ B) γ = A γ ⊎ B γ
