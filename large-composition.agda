{-

"Large" composition of fibrant types

-}
{-# OPTIONS --rewriting #-}
module large-composition where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.functions
open import Data.paths
open import Data.products
open import equivs
open import glueing
open import union

module Partial {ℓ} {Γ : Set ℓ}
  (S : Shape) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib (res Γ φ × ⟨ S ⟩))
  (X₀ : Fib Γ) (match : reindex' F (λ {(x , u) → (x , u) , r x}) ≡ reindex' X₀ fst)
  (s : Γ → ⟨ S ⟩)
  where

  singletonL : (x : Γ) (j : ⟨ S ⟩) → [ φ x ] → Σ A ∈ Set , Equiv A (X₀ .fst x)
  singletonL x j u =
    ( F .fst ((x , u) , j)
    , subst (Equiv (F .fst ((x , u) , j)))
      (appCong (cong fst match))
      (coerceEquiv S (reindex' F (λ i → ((x , u) , i)) .snd) j (r x))
    )

  singletonR : (x : Γ) → Σ A ∈ Set , Equiv A (X₀ .fst x)
  singletonR x =
    ( X₀ .fst x
    , idEquiv (reindex' X₀ (λ _ → x) .snd)
    )

  singletonEqLem : (x : Γ) → ∀ u
    → _≡_ {A = Σ Aα ∈ Fib Unit , Aα .fst tt ≡ X₀ .fst x}
      (reindex' F (λ _ → (x , u) , r x) , appCong (cong fst match))
      (reindex' X₀ (λ _ → x) , refl)
  singletonEqLem x u =
    Σext (cong (reindex' ◆ λ _ → x , u) match) uipImp

  abstract
    singletonEq : (x : Γ) → ∀ u → r x ≡ s x → singletonL x (s x) u ≡ singletonR x
    singletonEq x u eq =
      trans
        (cong
          (λ {((B , β) , eq) → (B tt , subst (Equiv (B tt)) eq (idEquiv β))})
          (singletonEqLem x u))
        (trans
          (cong
            {B = Σ A ∈ Set , Equiv A (X₀ .fst x)}
            (λ e →
              ( F .fst ((x , u) , r x)
              , subst (Equiv (F .fst ((x , u) , r x)))
                (appCong (cong fst match))
                e
              ))
             (coerceEquivCap S (reindex' F (λ i → ((x , u) , i)) .snd) (r x)))
          (cong (λ j → singletonL x j u) (symm eq)))

  singletons : (x : Γ) → [ φ x ∨ S ∋ r x ≈ s x ] → Σ A ∈ Set , Equiv A (X₀ .fst x)
  singletons x =
    ∨-rec (φ x) (S ∋ r x ≈ s x) (singletonL x (s x)) (λ _ → singletonR x) (singletonEq x)

  private
    ats : res Γ φ → res Γ φ × ⟨ S ⟩
    ats (x , u) = (x , u) , s x

    fst' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} → Σ Γ (A ×' B) → Σ Γ A
    fst' (x , a , b) = (x , a)

  match' : reindex' F (ats ∘ fst') ≡ reindex' X₀ fst
  match' =
    (trans
      (cong (reindex' ◆ fst') match)
      (cong (reindex' F) (funext λ {(x , u , eq) → Σext refl (symm eq)})))

  module Fib =
    FibUnion φ (λ x → S ∋ r x ≈ s x)
      {A = λ {(x , u∨eq) → singletons x u∨eq .fst}}
      (reindex' F ats .snd)
      (reindex' X₀ fst .snd)
      match'

  fib : Fib (res Γ (λ x → φ x ∨ S ∋ r x ≈ s x))
  fib = ((λ {(x , u∨eq) → singletons x u∨eq .fst}) , Fib.fib)

module _ {ℓ} {Γ : Set ℓ}
  (S : Shape) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib (res Γ φ × ⟨ S ⟩))
  (X₀ : Fib Γ) (match : reindex' F (λ {(x , u) → (x , u) , r x}) ≡ reindex' X₀ fst)
  where

  module _ (s : Γ → ⟨ S ⟩) where

    open Partial S r φ F X₀ match s

    LargeComp : Fib Γ
    LargeComp = SGlueFib (λ x → φ x ∨ S ∋ r x ≈ s x) fib X₀ (λ {(x , ueq) → singletons x ueq .snd})

    LargeCompMatch :
      reindex' F (λ {(x , u) → (x , u) , s x}) ≡ reindex' LargeComp fst
    LargeCompMatch =
      trans
        (cong
          (reindex' ◆ inl' φ (λ x → S ∋ r x ≈ s x))
          (SGlueFibStrictness (λ x → φ x ∨ S ∋ r x ≈ s x) fib X₀ (λ {(x , ueq) → singletons x ueq .snd})))
        (symm Fib.left')

  LargeCap : LargeComp r ≡ X₀
  LargeCap =
    trans
      (cong (reindex' ◆ f₀) Fib.right')
      (cong (reindex' ◆ (inr' φ (λ x → S ∋ r x ≈ r x) ∘ f₀))
        (symm (SGlueFibStrictness (λ x → φ x ∨ S ∋ r x ≈ r x) fib X₀ (λ {(x , ueq) → singletons x ueq .snd}))))
    where
    open Partial S r φ F X₀ match r

    f₀ : Γ → res Γ (λ x → S ∋ r x ≈ r x)
    f₀ x = x , refl

-- TODO stability under substitution
