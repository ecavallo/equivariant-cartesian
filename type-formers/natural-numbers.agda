{-

Fibrancy of the extensional type of natural numbers ℕ.

-}
module type-formers.natural-numbers where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.decidable

open import Agda.Builtin.Nat renaming (Nat to ℕ)

--↓ Standard decision procedure for equality in ℕ.

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

zero≢suc : ∀ n → ¬ (zero ≡ suc n)
zero≢suc n = subst Code ⦅–⦆ tt
  where
  Code : ℕ → Type
  Code zero = 𝟙
  Code (suc _) = 𝟘

suc≢zero : ∀ n → ¬ (suc n ≡ zero)
suc≢zero n = zero≢suc n ∘ sym

decideEqualityℕ : (m n : ℕ) → Decision (m ≡ n)
decideEqualityℕ zero zero = inl refl
decideEqualityℕ zero (suc n) = inr (zero≢suc n)
decideEqualityℕ (suc m) zero = inr (suc≢zero m)
decideEqualityℕ (suc m) (suc n) = (cong suc ⊎` (_∘ cong pred)) (decideEqualityℕ m n)

--↓ Decidable equality suffices to construct a fibration structure.

ℕFibStr : FibStr (λ (_ : 𝟙) → ℕ)
ℕFibStr = DecidableEqFibStr ℕ decideEqualityℕ

ℕᶠ : 𝟙 ⊢ᶠType lzero
ℕᶠ .fst _ = ℕ
ℕᶠ .snd = ℕFibStr
