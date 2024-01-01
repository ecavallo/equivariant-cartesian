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
infixl 3 _▷ˣ_ _,,_

--↓ Term judgment of the extensional type theory.

_⊢ˣ_ : (Γ : Type ℓ) (A : Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
(Γ ⊢ˣ A) = Π Γ A

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
