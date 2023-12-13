{-

Internal interpretation of extensional type theory.

Each universe Type ℓ of our ambient extensional type theory gives us an _internal_
interpretation of extensional type theory where contexts are elements of Type ℓ and
a type over Γ : Type ℓ is a family Γ → Type ℓ.

To build our interpretation of homotopy type theory, where contexts are again interpreted
as types Γ : Type ℓ and types are interpreted as families Γ → Type ℓ equipped with
_fibration structures_, it is convenient to have some suggestive notation for the internal
extensional type theory.

To disambiguate from definitions pertaining to the interpretation of _homotopy_ type
theory when necessary, we use the superscript ˣ to indicate extensional.

-}

module internal-extensional-type-theory where

open import prelude

private variable
  ℓ ℓ' ℓ'' : Level
  Γ Δ : Type ℓ

infix  1 _⊢_
infixl 3 _▷_ _,,_

--↓ Term judgment.

_⊢_ : (Γ : Type ℓ) (A : Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
(Γ ⊢ A) = Π Γ A

--↓ Context and substitution extension.

_▷_ : (Γ : Type ℓ) → (Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
Γ ▷ A = Σ Γ A

_,,_ : {A : Γ → Type ℓ''} (ρ : Δ → Γ) (a : Δ ⊢ A ∘ ρ) → (Δ → Γ ▷ A)
(ρ ,, a) δ .fst = ρ δ
(ρ ,, a) δ .snd = a δ

--↓ Suggestive notation for projections where used as substitutions.
--↓ In Agda's input mode, these are \MIp and \MIq respectively.

𝒑 : {Γ : Type ℓ} {A : Γ → Type ℓ} → Γ ▷ A → Γ
𝒑 = fst

𝒒 : {Γ : Type ℓ} {A : Γ → Type ℓ} → Γ ▷ A ⊢ A ∘ 𝒑
𝒒 = snd
