{-

Showing the universe is closed under type formers

-}
module universe.type-formers where

open import prelude
open import axioms
open import fibration.fibration

open import type-formers.pi
open import type-formers.sigma

open import universe.core
open import universe.fibrant

private variable
  ℓ : Level
  Γ : Type ℓ

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Σ-types
  ----------------------------------------------------------------------------------------

  universalΣᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
  universalΣᶠ = Σᶠ (Elᶠ ∘ᶠ fst) (Elᶠ ∘ᶠ λ (A , B , a) → B a)

  sigma : (a : 𝑼 ℓ) (b : El a → 𝑼 ℓ) → 𝑼 ℓ
  sigma a b = encode universalΣᶠ (a , b)

  sigmaᵁ : (a : Γ ⊢ᶠ 𝑼ᶠ ℓ) (b : Γ ▷ᶠ (Elᶠ ∘ᶠ a) ⊢ᶠ 𝑼ᶠ ℓ) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  sigmaᵁ a b x = sigma (a x) (curry b x)

  decodeSigma : (a : Γ ⊢ᶠ 𝑼ᶠ ℓ) (b : Γ ▷ᶠ (Elᶠ ∘ᶠ a) ⊢ᶠ 𝑼ᶠ ℓ)
    → decode (sigmaᵁ a b) ≡ Σᶠ (decode a) (decode b)
  decodeSigma a b =
    cong (_∘ᶠ (a ,, curry b)) (decodeEncode universalΣᶠ)
    ∙ reindexΣᶠ (a ,, curry b)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Π-types
  ----------------------------------------------------------------------------------------

  universalΠᶠ : (Σ A ∈ 𝑼 ℓ , (El A → 𝑼 ℓ)) ⊢ᶠType ℓ
  universalΠᶠ = Πᶠ (Elᶠ ∘ᶠ fst) (Elᶠ ∘ᶠ λ (A , B , a) → B a)

  pi : (a : 𝑼 ℓ) (b : El a → 𝑼 ℓ) → 𝑼 ℓ
  pi a b = encode universalΠᶠ (a , b)

  piᵁ : (a : Γ ⊢ᶠ 𝑼ᶠ ℓ) (b : Γ ▷ᶠ (Elᶠ ∘ᶠ a) ⊢ᶠ 𝑼ᶠ ℓ) → Γ ⊢ᶠ 𝑼ᶠ ℓ
  piᵁ a b x = pi (a x) (curry b x)

  decodePi : (a : Γ ⊢ᶠ 𝑼ᶠ ℓ) (b : Γ ▷ᶠ (Elᶠ ∘ᶠ a) ⊢ᶠ 𝑼ᶠ ℓ)
    → decode (piᵁ a b) ≡ Πᶠ (decode a) (decode b)
  decodePi a b =
    cong (_∘ᶠ (a ,, curry b)) (decodeEncode universalΠᶠ)
    ∙ reindexΠᶠ (a ,, curry b)

  ----------------------------------------------------------------------------------------
  -- The universe of fibrations is closed under Path types
  ----------------------------------------------------------------------------------------

  -- TODO
