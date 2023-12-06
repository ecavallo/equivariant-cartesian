{-

Showing the universe is closed under type formers

-}
module universe.type-formers where

open import prelude
open import axioms
open import fibration.fibration

open import type-formers.empty
open import type-formers.paths
open import type-formers.pi
open import type-formers.sigma
open import type-formers.unit

open import universe.core
open import universe.fibrant

private variable
  ℓ : Level
  Γ : Type ℓ

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations contains an empty type
  ----------------------------------------------------------------------------------------

  𝟘ᵁ : Γ ⊢ᶠ 𝑼ᶠ lzero
  𝟘ᵁ = encode 𝟘ᶠ ∘ cst tt

  El-𝟘ᵁ : Elᶠ (𝟘ᵁ {Γ = Γ}) ≡ 𝟘ᶠ
  El-𝟘ᵁ = cong (_∘ᶠ cst tt) (decodeEncode 𝟘ᶠ)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Σ-types
  ----------------------------------------------------------------------------------------

  universalΣᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
  universalΣᶠ = Σᶠ (Elᶠ fst) (Elᶠ λ (A , B , a) → B a)

  Σᵁ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Σᵁ A B = encode universalΣᶠ ∘ (A ,, curry B)

  El-Σ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
    → Elᶠ (Σᵁ A B) ≡ Σᶠ (Elᶠ A) (Elᶠ B)
  El-Σ A B =
    cong (_∘ᶠ (A ,, curry B)) (decodeEncode universalΣᶠ) ∙ reindexΣᶠ (A ,, curry B)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Path types
  ----------------------------------------------------------------------------------------

  universalPathᶠ : (Σ A ∈ 𝑼 ℓ , El A × El A) ⊢ᶠType ℓ
  universalPathᶠ = Pathᶠ (Elᶠ fst) (fst ∘ snd) (snd ∘ snd)

  Pathᵁ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Pathᵁ A a₀ a₁ = encode universalPathᶠ ∘ (A ,, (a₀ ,, a₁))

  El-Path : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (a₀ a₁ : Γ ⊢ᶠ Elᶠ A)
    → Elᶠ (Pathᵁ A a₀ a₁) ≡ Pathᶠ (Elᶠ A) a₀ a₁
  El-Path A a₀ a₁ =
    cong (_∘ᶠ (A ,, (a₀ ,, a₁))) (decodeEncode universalPathᶠ)
    ∙ reindexPathᶠ (A ,, (a₀ ,, a₁))

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Π-types
  ----------------------------------------------------------------------------------------

  universalΠᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
  universalΠᶠ = Πᶠ (Elᶠ fst) (Elᶠ λ (A , B , a) → B a)

  Πᵁ : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  Πᵁ A B = encode universalΠᶠ ∘ (A ,, curry B)

  El-Π : (A : Γ ⊢ᶠ 𝑼ᶠ ℓ) (B : Γ ▷ᶠ Elᶠ A ⊢ᶠ 𝑼ᶠ ℓ)
    → Elᶠ (Πᵁ A B) ≡ Πᶠ (Elᶠ A) (Elᶠ B)
  El-Π A B =
    cong (_∘ᶠ (A ,, curry B)) (decodeEncode universalΠᶠ) ∙ reindexΠᶠ (A ,, curry B)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations contains a unit type
  ----------------------------------------------------------------------------------------

  𝟙ᵁ : Γ ⊢ᶠ 𝑼ᶠ lzero
  𝟙ᵁ = encode 𝟙ᶠ ∘ cst tt

  El-𝟙ᵁ : Elᶠ (𝟙ᵁ {Γ = Γ}) ≡ 𝟙ᶠ
  El-𝟙ᵁ = cong (_∘ᶠ cst tt) (decodeEncode 𝟙ᶠ)
