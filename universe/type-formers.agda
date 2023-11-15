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

private variable ℓ' : Level

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------
  -- The universe is closed under Σ-types
  ----------------------------------------------------------------------
  ΣIsFibUniversal :
    isFib {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} (λ (A , B) → Σ x ∈ El A , El (B x))
  ΣIsFibUniversal =
    ΣIsFib (reindex υ fst) (reindex υ (λ ((A , B) , a) → B a))

  sigma : (a : U ℓ) (b : El a → U ℓ) → U ℓ
  sigma a b = encode (_ , ΣIsFibUniversal) (a , b)

  sigmaᴵ : {Γ : Set ℓ'}
    (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ) → (Γ → U ℓ)
  sigmaᴵ a b x = sigma (a x) (curry b x)

  decodeSigma : {Γ : Set ℓ'}
    (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ)
    → decode (sigmaᴵ a b) ≡ FibΣ (decode a) (decode b)
  decodeSigma a b =
    cong
      (reindexFib ◆ λ x → (a x , curry b x))
      {x = decode (encode (_ , ΣIsFibUniversal))}
      (decodeEncode (_ , ΣIsFibUniversal))
    ∙
    reindexFibΣ
      {Γ = Σ A ∈ U ℓ , (El A → U ℓ)}
      (reindexFib (El , υ) fst)
      (reindexFib (El , υ) (λ ((A , B) , a) → B a))
      (a ,, curry b)

  ----------------------------------------------------------------------
  -- The universe is closed under Π-types
  ----------------------------------------------------------------------
  ΠIsFibUniversal :
    isFib {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} (λ (A , B) → (x : El A) → El (B x))
  ΠIsFibUniversal =
    ΠIsFib (reindex υ fst) (reindex υ (λ ((A , B) , a) → B a))

  pi : (a : U ℓ) (b : El a → U ℓ) → U ℓ
  pi a b = encode (_ , ΠIsFibUniversal) (a , b)

  piᴵ : {Γ : Set ℓ'}
    (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ) → (Γ → U ℓ)
  piᴵ a b x = pi (a x) (curry b x)

  decodePi : {Γ : Set ℓ'}
    (a : Γ → U ℓ) (b : Σ Γ (El ∘ a) → U ℓ)
    → decode (piᴵ a b) ≡ FibΠ (decode a) (decode b)
  decodePi a b =
    cong
      (reindexFib ◆ λ x → (a x , curry b x))
      {x = decode (encode (_ , ΠIsFibUniversal))}
      (decodeEncode (_ , ΠIsFibUniversal))
    ∙
    reindexFibΠ
      {Γ = Σ A ∈ U ℓ , (El A → U ℓ)}
      (reindexFib (El , υ) fst)
      (reindexFib (El , υ) (λ ((A , B) , a) → B a))
      (a ,, curry b)

  -- TODO other types
