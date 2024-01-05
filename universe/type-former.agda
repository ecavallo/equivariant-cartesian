{-

Showing the universe is closed under type formers

-}
module universe.type-former where

open import basic
open import internal-extensional-type-theory
open import axiom
open import fibration.fibration

open import type-former.empty
open import type-former.natural-number
open import type-former.path
open import type-former.pi
open import type-former.sigma
open import type-former.swan-identity
open import type-former.unit

open import universe.core
open import universe.fibrant

private variable
  ℓ : Level
  Γ : Type ℓ

----------------------------------------------------------------------------------------
-- The universe of fibrations contains an empty type.
----------------------------------------------------------------------------------------

𝟘ᵁ : 𝑼 lzero
𝟘ᵁ = encode 𝟘ᶠ tt

𝟘ᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
𝟘ᵁᶠ _ = 𝟘ᵁ

opaque
  El-𝟘ᶠ : Elᶠ (𝟘ᵁᶠ {Γ = Γ}) ≡ 𝟘ᶠ
  El-𝟘ᶠ = cong (_∘ᶠ cst tt) (decodeEncode 𝟘ᶠ)

----------------------------------------------------------------------------------------
-- The universe of fibrations contains a unit type.
----------------------------------------------------------------------------------------

𝟙ᵁ : 𝑼 lzero
𝟙ᵁ = encode 𝟙ᶠ tt

𝟙ᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
𝟙ᵁᶠ _ = 𝟙ᵁ

opaque
  El-𝟙ᶠ : Elᶠ (𝟙ᵁᶠ {Γ = Γ}) ≡ 𝟙ᶠ
  El-𝟙ᶠ = cong (_∘ᶠ cst tt) (decodeEncode 𝟙ᶠ)

----------------------------------------------------------------------------------------
-- The universe of fibrations contains a natural number type.
----------------------------------------------------------------------------------------

ℕᵁ : 𝑼 lzero
ℕᵁ = encode ℕᶠ tt

ℕᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
ℕᵁᶠ _ = ℕᵁ

opaque
  El-ℕᶠ : Elᶠ (ℕᵁᶠ {Γ = Γ}) ≡ ℕᶠ
  El-ℕᶠ = cong (_∘ᶠ cst tt) (decodeEncode ℕᶠ)


module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Σ-types.
  ----------------------------------------------------------------------------------------

  private
    universalΣᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
    universalΣᶠ = Σᶠ (Elᶠ fst) (Elᶠ λ (A , B , a) → B a)

  Σᵁ : (A : 𝑼 ℓ) (B : El A → 𝑼 ℓ) → 𝑼 ℓ
  Σᵁ A B = encode universalΣᶠ (A , B)

  Σᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ) → (Γ ⊢ᶠ 𝑼ᶠ ℓ)
  Σᵁᶠ A B γ = Σᵁ (A γ) (curry B γ)

  opaque
    El-Σᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
      → Elᶠ (Σᵁᶠ A B) ≡ Σᶠ (Elᶠ A) (Elᶠ B)
    El-Σᶠ A B =
      cong (_∘ᶠ (A ,ˣ curry B)) (decodeEncode universalΣᶠ) ∙ reindexΣᶠ (A ,ˣ curry B)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Path types.
  ----------------------------------------------------------------------------------------

  private
    universalPathᶠ : (Σ A ∈ 𝑼 ℓ , El A × El A) ⊢ᶠType ℓ
    universalPathᶠ = Pathᶠ (Elᶠ fst) (fst ∘ snd) (snd ∘ snd)

  Pathᵁ : (A : 𝑼 ℓ) (a₀ a₁ : El A) → 𝑼 ℓ
  Pathᵁ A a₀ a₁ = encode universalPathᶠ (A , (a₀ , a₁))

  Pathᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Pathᵁᶠ A a₀ a₁ γ = Pathᵁ (A γ) (a₀ γ) (a₁ γ)

  opaque
    El-Pathᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A)
      → Elᶠ (Pathᵁᶠ A a₀ a₁) ≡ Pathᶠ (Elᶠ A) a₀ a₁
    El-Pathᶠ A a₀ a₁ =
      cong (_∘ᶠ (A ,ˣ (a₀ ,ˣ a₁))) (decodeEncode universalPathᶠ)
      ∙ reindexPathᶠ (A ,ˣ (a₀ ,ˣ a₁))

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Π-types.
  ----------------------------------------------------------------------------------------

  private
    universalΠᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
    universalΠᶠ = Πᶠ (Elᶠ fst) (Elᶠ λ (A , B , a) → B a)

  Πᵁ : (A : 𝑼 ℓ) (B : El A → 𝑼 ℓ) → 𝑼 ℓ
  Πᵁ A B = encode universalΠᶠ (A , B)

  Πᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Πᵁᶠ A B γ = Πᵁ (A γ) (curry B γ)

  opaque
    El-Πᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
      → Elᶠ (Πᵁᶠ A B) ≡ Πᶠ (Elᶠ A) (Elᶠ B)
    El-Πᶠ A B =
      cong (_∘ᶠ (A ,ˣ curry B)) (decodeEncode universalΠᶠ) ∙ reindexΠᶠ (A ,ˣ curry B)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Swan identity types, assuming
  -- cofibration extensionality and closure of Cof under Σ-types.
  ----------------------------------------------------------------------------------------

  module SwanIdentityᵁ (@♭ ext : CofExtensionality) (@♭ dom : CofHasΣ) where
    open SwanIdentity ext dom

    private
      universalIdᶠ : (Σ A ∈ 𝑼 ℓ , El A × El A) ⊢ᶠType ℓ
      universalIdᶠ = Idᶠ (Elᶠ fst) (fst ∘ snd) (snd ∘ snd)

    Idᵁ : (A : 𝑼 ℓ) (a₀ a₁ : El A) → 𝑼 ℓ
    Idᵁ A a₀ a₁ = encode universalIdᶠ (A , (a₀ , a₁))

    Idᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A) → Γ ⊢ᶠ 𝑼ᶠ ℓ
    Idᵁᶠ A a₀ a₁ γ = Idᵁ (A γ) (a₀ γ) (a₁ γ)

    opaque
      El-Idᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A)
        → Elᶠ (Idᵁᶠ A a₀ a₁) ≡ Idᶠ (Elᶠ A) a₀ a₁
      El-Idᶠ A a₀ a₁ =
        cong (_∘ᶠ (A ,ˣ (a₀ ,ˣ a₁))) (decodeEncode universalIdᶠ)
        ∙ reindexIdᶠ (A ,ˣ (a₀ ,ˣ a₁))
