{-

Showing the universe is closed under type formers

-}
{-# OPTIONS --rewriting #-}
module universe.types where

open import prelude
open import shape
open import cofprop
open import fibrations

open import Data.products
open import Data.functions

open import universe.axioms
open import universe.core

----------------------------------------------------------------------
-- The universe is closed under Σ-types
----------------------------------------------------------------------
FibΣUniversal : ∀ {@♭ ℓ} →
  isFib {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} (λ{ (A , B) → Σ x ∈ El A , El (B x) })
FibΣUniversal =
  FibΣ (reindex El υ fst) (reindex El υ (λ {((A , B) , a) → B a}))

sigma : ∀ {@♭ ℓ} (a : U ℓ) (b : El a → U ℓ) → U ℓ
sigma a b = encode (_ , FibΣUniversal) (a , b)

sigma' : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → (Γ → U ℓ')
sigma' a b x = sigma (a x) (curry b x)

decodeSigma : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → decode (sigma' a b) ≡ FibΣ' (decode a) (decode b)
decodeSigma {ℓ' = ℓ'} a b =
  trans
    (reindexΣ'
      {Γ = Σ A ∈ U ℓ' , (El A → U ℓ')}
      (reindex' (El , υ) fst)
      (reindex' (El , υ) (λ {((A , B) , a) → B a}))
      (λ x → (a x , curry b x)))
    (cong
      (reindex' ◆ λ x → (a x , curry b x))
      {x = decode (encode (_ , FibΣUniversal))}
      (decodeEncode (_ , FibΣUniversal)))

----------------------------------------------------------------------
-- The universe is closed under Π-types
----------------------------------------------------------------------
FibΠUniversal : ∀ {@♭ ℓ} →
  isFib {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} (λ{ (A , B) → (x : El A) → El (B x)})
FibΠUniversal =
  FibΠ (reindex El υ fst) (reindex El υ (λ {((A , B) , a) → B a}))

pi : ∀ {@♭ ℓ} → (a : U ℓ) (b : El a → U ℓ) → U ℓ
pi a b = encode (_ , FibΠUniversal) (a , b)

pi' : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → (Γ → U ℓ')
pi' a b x = pi (a x) (curry b x)

decodePi : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → decode (pi' a b) ≡ FibΠ' (decode a) (decode b)
decodePi {ℓ' = ℓ'} a b =
  trans
    (reindexΠ'
      {Γ = Σ A ∈ U ℓ' , (El A → U ℓ')}
      (reindex' (El , υ) fst)
      (reindex' (El , υ) (λ {((A , B) , a) → B a}))
      (λ x → (a x , curry b x)))
    (cong
      (reindex' ◆ λ x → (a x , curry b x))
      {x = decode (encode (_ , FibΠUniversal))}
      (decodeEncode (_ , FibΠUniversal)))

-- TODO other types
