{-

Propositional truncation (for the extensional type theory)

-}
{-# OPTIONS --rewriting #-}
module axioms.truncation where

open import prelude

private variable ℓ ℓ' : Level

----------------------------------------------------------------------
-- Propositional truncation
----------------------------------------------------------------------

postulate
  ∥_∥ : Set ℓ → Set ℓ

module _ {A : Set ℓ} where
  postulate
    ∣_∣ : A → ∥ A ∥

    trunc : isProp ∥ A ∥

    ∥∥-rec : (P : Set ℓ')
      (f : A → P)
      .(p : ∀ a b → f a ≡ f b)
      → ---------------
      ∥ A ∥ → P

    ∥∥-rec-β : ∀ (P : Set ℓ') f p a
      → ∥∥-rec P f p ∣ a ∣ ≡ f a

    ∥∥-elim : (P : ∥ A ∥ → Set ℓ')
      (f : (a : A) → P ∣ a ∣)
      .(p : ∀ a b → subst P (trunc ∣ a ∣ ∣ b ∣) (f a) ≡ f b)
      → ---------------
      (t : ∥ A ∥) → P t

    ∥∥-elim-β : ∀ (P : ∥ A ∥ → Set ℓ') f p a
      → ∥∥-elim P f p ∣ a ∣ ≡ f a

    {-# REWRITE ∥∥-rec-β ∥∥-elim-β #-}

∥_∥` : {A : Set ℓ} {B : Set ℓ'}
  → (A → B) → ∥ A ∥ → ∥ B ∥
∥_∥` f = ∥∥-rec _ (∣_∣ ∘ f) (λ _ _ → trunc _ _)
