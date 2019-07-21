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
FibΣUniversal :
  isFib {Γ = Σ A ∈ U , (El A → U)} (λ{ (A , B) → Σ x ∈ El A , El (B x) })
FibΣUniversal =
  FibΣ (reindex El υ fst) (reindex El υ (λ {((A , B) , a) → B a}))

sigma : (a : U) (b : El a → U) → U
sigma a b = encode (_ , FibΣUniversal) (a , b)

sigma' : ∀ {ℓ} {Γ : Set ℓ}
  (a : Γ → U) (b : Σ Γ (El ∘ a) → U)
  → (Γ → U)
sigma' a b x = sigma (a x) (curry b x)

decodeSigma : ∀ {ℓ} {Γ : Set ℓ}
  (a : Γ → U) (b : Σ Γ (El ∘ a) → U)
  → decode (sigma' a b) ≡ FibΣ' (decode a) (decode b)
decodeSigma a b =
  trans
    (reindexΣ'
      {Γ = Σ A ∈ U , (El A → U)}
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
FibΠUniversal :
  isFib {Γ = Σ A ∈ U , (El A → U)} (λ{ (A , B) → (x : El A) → El (B x)})
FibΠUniversal =
  FibΠ (reindex El υ fst) (reindex El υ (λ {((A , B) , a) → B a}))

pi : (a : U) (b : El a → U) → U
pi a b = encode (_ , FibΠUniversal) (a , b)

pi' : ∀ {ℓ} {Γ : Set ℓ}
  (a : Γ → U) (b : Σ Γ (El ∘ a) → U)
  → (Γ → U)
pi' a b x = pi (a x) (curry b x)

decodePi : ∀ {ℓ} {Γ : Set ℓ}
  (a : Γ → U) (b : Σ Γ (El ∘ a) → U)
  → decode (pi' a b) ≡ FibΠ' (decode a) (decode b)
decodePi a b =
  trans
    (reindexΠ'
      {Γ = Σ A ∈ U , (El A → U)}
      (reindex' (El , υ) fst)
      (reindex' (El , υ) (λ {((A , B) , a) → B a}))
      (λ x → (a x , curry b x)))
    (cong
      (reindex' ◆ λ x → (a x , curry b x))
      {x = decode (encode (_ , FibΠUniversal))}
      (decodeEncode (_ , FibΠUniversal)))

-- TODO other types
