{-

Showing the universe is closed under type formers

-}
module universe.type-former where

open import prelude
open import axiom
open import fibration.fibration

open import type-former.empty
open import type-former.path
open import type-former.pi
open import type-former.sigma
open import type-former.unit

open import universe.core
open import universe.fibrant

private variable
  ℓ : Level
  Γ : Type ℓ

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations contains an empty type
  ----------------------------------------------------------------------------------------

  𝟘ᵁ : 𝑼 lzero
  𝟘ᵁ = encode 𝟘ᶠ tt

  𝟘ᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
  𝟘ᵁᶠ _ = 𝟘ᵁ

  opaque
    Elᶠ-𝟘ᵁ : Elᶠ (𝟘ᵁᶠ {Γ = Γ}) ≡ 𝟘ᶠ
    Elᶠ-𝟘ᵁ = cong (_∘ᶠ cst tt) (decodeEncode 𝟘ᶠ)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Σ-types
  ----------------------------------------------------------------------------------------

  private
    universalΣᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
    universalΣᶠ = Σᶠ (Elᶠ fst) (Elᶠ λ (A , B , a) → B a)

  Σᵁ : (A : 𝑼 ℓ) (B : El A → 𝑼 ℓ) → 𝑼 ℓ
  Σᵁ A B = encode universalΣᶠ (A , B)

  Σᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ) → (Γ ⊢ᶠ 𝑼ᶠ ℓ)
  Σᵁᶠ A B γ = Σᵁ (A γ) (curry B γ)

  opaque
    Elᶠ-Σᵁ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
      → Elᶠ (Σᵁᶠ A B) ≡ Σᶠ (Elᶠ A) (Elᶠ B)
    Elᶠ-Σᵁ A B =
      cong (_∘ᶠ (A ,ᴵ curry B)) (decodeEncode universalΣᶠ) ∙ reindexΣᶠ (A ,ᴵ curry B)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Path types
  ----------------------------------------------------------------------------------------

  private
    universalPathᶠ : (Σ A ∈ 𝑼 ℓ , El A × El A) ⊢ᶠType ℓ
    universalPathᶠ = Pathᶠ (Elᶠ fst) (fst ∘ snd) (snd ∘ snd)

  Pathᵁ : (A : 𝑼 ℓ) (a₀ a₁ : El A) → 𝑼 ℓ
  Pathᵁ A a₀ a₁ = encode universalPathᶠ (A , (a₀ , a₁))

  Pathᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Pathᵁᶠ A a₀ a₁ γ = Pathᵁ (A γ) (a₀ γ) (a₁ γ)

  opaque
    El-Path : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A)
      → Elᶠ (Pathᵁᶠ A a₀ a₁) ≡ Pathᶠ (Elᶠ A) a₀ a₁
    El-Path A a₀ a₁ =
      cong (_∘ᶠ (A ,ᴵ (a₀ ,ᴵ a₁))) (decodeEncode universalPathᶠ)
      ∙ reindexPathᶠ (A ,ᴵ (a₀ ,ᴵ a₁))

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Π-types
  ----------------------------------------------------------------------------------------

  private
    universalΠᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
    universalΠᶠ = Πᶠ (Elᶠ fst) (Elᶠ λ (A , B , a) → B a)

  Πᵁ : (A : 𝑼 ℓ) (B : El A → 𝑼 ℓ) → 𝑼 ℓ
  Πᵁ A B = encode universalΠᶠ (A , B)

  Πᵁᶠ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Πᵁᶠ A B γ = Πᵁ (A γ) (curry B γ)

  opaque
    El-Πᵁ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
      → Elᶠ (Πᵁᶠ A B) ≡ Πᶠ (Elᶠ A) (Elᶠ B)
    El-Πᵁ A B =
      cong (_∘ᶠ (A ,ᴵ curry B)) (decodeEncode universalΠᶠ) ∙ reindexΠᶠ (A ,ᴵ curry B)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations contains a unit type
  ----------------------------------------------------------------------------------------

  𝟙ᵁ : 𝑼 lzero
  𝟙ᵁ = encode 𝟙ᶠ tt

  𝟙ᵁᶠ : Γ ⊢ᶠ 𝑼ᶠ lzero
  𝟙ᵁᶠ _ = 𝟙ᵁ

  opaque
    El-𝟙ᵁ : Elᶠ (𝟙ᵁᶠ {Γ = Γ}) ≡ 𝟙ᶠ
    El-𝟙ᵁ = cong (_∘ᶠ cst tt) (decodeEncode 𝟙ᶠ)
