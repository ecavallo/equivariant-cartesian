{-

Propositional truncation (for the extensional type theory)

-}
{-# OPTIONS --rewriting #-}
module axioms.truncation where

open import prelude

----------------------------------------------------------------------
-- Propositional truncation
----------------------------------------------------------------------

postulate
  ∥_∥ : ∀ {ℓ} → Set ℓ → Set ℓ

module _ {ℓ : Level} {A : Set ℓ} where
  postulate
    ∣_∣ : A → ∥ A ∥

    trunc : (t u : ∥ A ∥) → t ≡ u

    ∥∥-rec : ∀ {ℓ'}
      (P : Set ℓ')
      (f : A → P)
      (p : ∀ a b → f a ≡ f b)
      → ---------------
      ∥ A ∥ → P

    ∥∥-rec-β : ∀ {ℓ'} (P : Set ℓ') f p → (a : A)
      → ∥∥-rec P f p ∣ a ∣ ≡ f a

    ∥∥-elim : ∀ {ℓ'}
      (P : ∥ A ∥ → Set ℓ')
      (f : (a : A) → P ∣ a ∣)
      (p : ∀ a b → subst P (trunc ∣ a ∣ ∣ b ∣) (f a) ≡ f b)
      → ---------------
      (t : ∥ A ∥) → P t

    ∥∥-elim-β : ∀ {ℓ'} (P : ∥ A ∥ → Set ℓ') f p → (a : A)
      → ∥∥-elim P f p ∣ a ∣ ≡ f a

    {-# REWRITE ∥∥-rec-β ∥∥-elim-β #-}
