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

----------------------------------------------------------------------
-- The universe is closed under Σ-types
----------------------------------------------------------------------
ΣIsFibUniversal : ∀ {@♭ ℓ} →
  isFib {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} (λ{ (A , B) → Σ x ∈ El A , El (B x) })
ΣIsFibUniversal =
  ΣIsFib (reindex El υ fst) (reindex El υ (λ {((A , B) , a) → B a}))

sigma : ∀ {@♭ ℓ} (a : U ℓ) (b : El a → U ℓ) → U ℓ
sigma a b = encode (_ , ΣIsFibUniversal) (a , b)

sigma' : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → (Γ → U ℓ')
sigma' a b x = sigma (a x) (curry b x)

decodeSigma : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → decode (sigma' a b) ≡ FibΣ (decode a) (decode b)
decodeSigma {ℓ' = ℓ'} a b =
  cong
    (reindexFib ◆ λ x → (a x , curry b x))
    {x = decode (encode (_ , ΣIsFibUniversal))}
    (decodeEncode (_ , ΣIsFibUniversal))
  ∙
  reindexFibΣ
    {Γ = Σ A ∈ U ℓ' , (El A → U ℓ')}
    (reindexFib (El , υ) fst)
    (reindexFib (El , υ) (λ {((A , B) , a) → B a}))
    (λ x → (a x , curry b x))

----------------------------------------------------------------------
-- The universe is closed under Π-types
----------------------------------------------------------------------
ΠIsFibUniversal : ∀ {@♭ ℓ} →
  isFib {Γ = Σ A ∈ U ℓ , (El A → U ℓ)} (λ{ (A , B) → (x : El A) → El (B x)})
ΠIsFibUniversal =
  ΠIsFib (reindex El υ fst) (reindex El υ (λ {((A , B) , a) → B a}))

pi : ∀ {@♭ ℓ} → (a : U ℓ) (b : El a → U ℓ) → U ℓ
pi a b = encode (_ , ΠIsFibUniversal) (a , b)

pi' : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → (Γ → U ℓ')
pi' a b x = pi (a x) (curry b x)

decodePi : ∀ {ℓ} {@♭ ℓ'} {Γ : Set ℓ}
  (a : Γ → U ℓ') (b : Σ Γ (El ∘ a) → U ℓ')
  → decode (pi' a b) ≡ FibΠ (decode a) (decode b)
decodePi {ℓ' = ℓ'} a b =
  cong
    (reindexFib ◆ λ x → (a x , curry b x))
    {x = decode (encode (_ , ΠIsFibUniversal))}
    (decodeEncode (_ , ΠIsFibUniversal))
  ∙
  reindexFibΠ
    {Γ = Σ A ∈ U ℓ' , (El A → U ℓ')}
    (reindexFib (El , υ) fst)
    (reindexFib (El , υ) (λ {((A , B) , a) → B a}))
    (λ x → (a x , curry b x))

-- TODO other types
