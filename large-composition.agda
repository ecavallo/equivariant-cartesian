{-

Composition in the "multiverse"

-}
{-# OPTIONS --rewriting #-}
module large-composition where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.functions
open import Data.paths
open import equivs
open import glueing
open import union

module _ {ℓ} {Γ : Set ℓ}
  (S : Shape) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib (res Γ φ × ⟨ S ⟩))
  (X₀ : Σ A ∈ Fib Γ , reindex' F (λ {(x , u) → (x , u) , r x}) ≡ reindex' A fst)
  where

  module Large (s : Γ → ⟨ S ⟩) where

    singletonL : (x : Γ) (j : ⟨ S ⟩) → [ φ x ] → Σ A ∈ Set , Equiv A (X₀ .fst .fst x)
    singletonL x j u =
      ( F .fst ((x , u) , j)
      , subst (λ C → Equiv (F .fst ((x , u) , j)) C)
        (appCong (cong fst (X₀ .snd)))
        (coerceEquiv S (reindex' F (λ i → ((x , u) , i)) .snd) j (r x))
      )

    singletonR : (x : Γ) → r x ≡ s x → Σ A ∈ Set , Equiv A (X₀ .fst .fst x)
    singletonR x eq =
      ( X₀ .fst .fst x
      , idEquiv (reindex' (X₀ .fst) (λ {tt → x}) .snd)
      )

    singletonEq : (x : Γ) → ∀ u eq → singletonL x (s x) u ≡ singletonR x eq
    singletonEq x u eq =
      trans
        (cong
          {A = Σ Aα ∈ Fib Unit , Aα .fst tt ≡ X₀ .fst .fst x}
          {B = Σ A ∈ Set , Equiv A (X₀ .fst .fst x)}
          (λ {((B , β) , eq) →
            (B tt , subst (Equiv (B tt)) eq (idEquiv β))})
          {x = reindex' F (λ {tt → (x , u) , r x}) , appCong (cong fst (X₀ .snd))}
          {y = reindex' (X₀ .fst) (λ {tt → x}) , refl}
          (Σext
            (cong (reindex' ◆ λ {tt → (x , u)}) (X₀ .snd))
            uipImp))
        (trans
          (cong
            {B = Σ A ∈ Set , Equiv A (X₀ .fst .fst x)}
            (λ e →
              ( F .fst ((x , u) , r x)
              , subst (Equiv (F .fst ((x , u) , r x)))
                (appCong (cong fst (X₀ .snd)))
                e
              ))
             (coerceEquivCap S (reindex' F (λ i → ((x , u) , i)) .snd) (r x)))
          (cong (λ j → singletonL x j u) (symm eq)))
    
    singletons : (x : Γ) → [ φ x ∨ S ∋ r x ≈ s x ] → Σ A ∈ Set , Equiv A (X₀ .fst .fst x)
    singletons x =
      ∨-rec (φ x) (S ∋ r x ≈ s x) (singletonL x (s x)) (singletonR x) (singletonEq x)

    module Fib =
      FibUnion φ (λ x → S ∋ r x ≈ s x)
        {A = λ {(x , u∨eq) → singletons x u∨eq .fst}}
        (reindex' F (λ {(x , u) → (x , u) , s x}) .snd)
        (reindex' (X₀ .fst) fst .snd)
        (trans
          (cong (λ C → reindex' C (λ {(x , u , rs) → x , u})) (X₀ .snd))
          (cong (reindex' F) (funext λ {(x , u , rs) → Σext refl (symm rs)})))

    abstract
      fib : Fib (res Γ (λ x → φ x ∨ S ∋ r x ≈ s x))
      fib = ((λ {(x , u∨eq) → singletons x u∨eq .fst}) , Fib.fib)

      left : reindex' fib (id× (∣_∣ ∘ inl)) ≡ reindex' F (λ {(x , u) → (x , u) , s x})
      left = Fib.left'

      right : reindex' fib (id× (∣_∣ ∘ inr)) ≡ reindex' (X₀ .fst) fst
      right = Fib.right'

      equiv : ∀ x uveq → Equiv (fib .fst (x , uveq)) (X₀ .fst .fst x)
      equiv x uveq = singletons x uveq .snd

  LargeComp : (s : Γ → ⟨ S ⟩)
      → Σ A ∈ Fib Γ , reindex' F (λ {(x , u) → (x , u) , s x}) ≡ reindex' A fst
  LargeComp s =
    ( SGlueFib (λ x → φ x ∨ S ∋ r x ≈ s x) fib (X₀ .fst) (uncurry equiv)
    , trans
        (cong
          (reindex' ◆ id× (∣_∣ ∘ inl))
          (SGlueFibStrictness (λ x → φ x ∨ S ∋ r x ≈ s x) fib (X₀ .fst) (uncurry equiv)))
        (symm left)
    )
    where
    open Large s

  LargeCap : LargeComp r .fst ≡ X₀ .fst
  LargeCap =
    trans
      (cong (reindex' ◆ λ x → x , refl) right)
      (cong (reindex' ◆ λ x → x , ∣ inr refl ∣)
        (symm (SGlueFibStrictness (λ x → φ x ∨ S ∋ r x ≈ r x) fib (X₀ .fst) (uncurry equiv))))
    where
    open Large r

  -- TODO stability under substitution
