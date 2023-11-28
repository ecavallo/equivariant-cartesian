{-

Showing the universe is closed under type formers

-}
{-# OPTIONS --rewriting #-}
module universe.type-formers where

open import prelude
open import axioms
open import fibration.fibration

open import type-formers.pi
open import type-formers.sigma

open import universe.core

private variable
  ℓ' : Level
  Γ : Type ℓ'

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------------------------
  -- The universe is closed under Σ-types
  ----------------------------------------------------------------------------------------

  universalΣᶠ : (Σ A ∈ U ℓ , (El A → U ℓ)) ⊢ᶠType ℓ
  universalΣᶠ = Σᶠ (Elᶠ ∘ᶠ fst) (Elᶠ ∘ᶠ λ ((A , B) , a) → B a)

  sigma : (a : U ℓ) (b : El a → U ℓ) → U ℓ
  sigma a b = encode universalΣᶠ (a , b)

  sigmaᴵ : (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ) → (Γ → U ℓ)
  sigmaᴵ a b x = sigma (a x) (curry b x)

  decodeSigma : (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ)
    → decode (sigmaᴵ a b) ≡ Σᶠ (decode a) (decode b)
  decodeSigma a b =
    cong
      (_∘ᶠ (a ,, curry b))
      {x = decode (encode universalΣᶠ)}
      (decodeEncode universalΣᶠ)
    ∙
    reindexΣᶠ {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} _ _ (a ,, curry b)

  ----------------------------------------------------------------------------------------
  -- The universe is closed under Π-types
  ----------------------------------------------------------------------------------------

  universalΠᶠ : (Σ A ∈ U ℓ , (El A → U ℓ)) ⊢ᶠType ℓ
  universalΠᶠ = Πᶠ (Elᶠ ∘ᶠ fst) (Elᶠ ∘ᶠ λ ((A , B) , a) → B a)

  pi : (a : U ℓ) (b : El a → U ℓ) → U ℓ
  pi a b = encode universalΠᶠ (a , b)

  piᴵ : (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ) → (Γ → U ℓ)
  piᴵ a b x = pi (a x) (curry b x)

  decodePi : (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ)
    → decode (piᴵ a b) ≡ Πᶠ (decode a) (decode b)
  decodePi a b =
    cong
      (_∘ᶠ (a ,, curry b))
      {x = decode (encode universalΠᶠ)}
      (decodeEncode universalΠᶠ)
    ∙
    reindexΠᶠ {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} _ _ (a ,, curry b)

  -- TODO other types
