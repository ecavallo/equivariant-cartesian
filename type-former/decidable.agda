{-

Fibrancy of closed types with decidable equality.

This construction depends on the tinyness of the interval, more precisely the consequence
that dependent product over a shape commutes with coproducts.

-}
module type-former.decidable where

open import basic
open import axiom
open import cofibration
open import fibration.fibration
open import tiny.preserves-coproduct

private variable
  ℓ : Level

--↓ Type of decision procedures for a type

Decision : Type ℓ → Type ℓ
Decision A = A ⊎ ¬ A

--↓ Fibration structure from a decision procedure for equality.
--↓ The filler for any open box is simply taken to be the box's cap.

module _ {@♭ ℓ} (A : Type ℓ) (decEq : (a a' : A) → Decision (a ≡ a')) where

  DecidableEqFibStr : FibStr (λ (_ : 𝟙) → A)
  DecidableEqFibStr .lift S γ r box .fill s .out = box .cap .out
  DecidableEqFibStr .lift S γ r box .fill s .out≡ u = lemma decision
    where
    decision = shape→⊎ S (λ i → decEq (box .tube i u) (box .cap .out))

    lemma : _ ⊎ _ → box .tube s u ≡ box .cap .out
    lemma (inl eq) = eq s
    lemma (inr neq) = 𝟘-rec (neq r (box .cap .out≡ u))
  DecidableEqFibStr .lift _ _ _ _ .cap≡ = refl
  DecidableEqFibStr .vary _ _ _ _ _ _ _ = refl
