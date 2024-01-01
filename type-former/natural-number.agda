{-

Fibrancy of the extensional type of natural numbers ℕ.

-}
module type-former.natural-number where

open import basic
open import internal-extensional-type-theory
open import axiom
open import fibration.fibration
open import type-former.decidable

open import Agda.Builtin.Nat renaming (Nat to ℕ)

private variable
  ℓ : Level
  Γ : Type ℓ

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

ℕFibStr : FibStr (λ (_ : Γ) → ℕ)
ℕFibStr = DecidableEqFibStr ℕ decideEqualityℕ ∘ᶠˢ cst tt

ℕᶠ : Γ ⊢ᶠType lzero
ℕᶠ .fst _ = ℕ
ℕᶠ .snd = ℕFibStr

--↓ Introduction.

zeroᶠ : Γ ⊢ᶠ ℕᶠ
zeroᶠ _ = zero

sucᶠ :
  (n : Γ ⊢ᶠ ℕᶠ)
  → Γ ⊢ᶠ ℕᶠ
sucᶠ n γ = suc (n γ)

--↓ Elimination.

ℕ-elimᶠ :
  (P : Γ ▷ᶠ ℕᶠ ⊢ᶠType ℓ)
  (z : Γ ⊢ᶠ P ∘ᶠ (id ,, zeroᶠ))
  (s : Γ ▷ᶠ ℕᶠ ▷ᶠ P ⊢ᶠ P ∘ᶠ (𝒑 ∘ 𝒑 ,, sucᶠ (𝒒 ∘ 𝒑)))
  (n : Γ ⊢ᶠ ℕᶠ)
  → Γ ⊢ᶠ P ∘ᶠ (id ,, n)
ℕ-elimᶠ P z s n γ = elim (n γ)
  where
  elim : ∀ m → P $ᶠ (γ , m)
  elim zero = z γ
  elim (suc m) = s ((γ , m) , elim m)
