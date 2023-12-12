{-

Propositional truncation (for the extensional type theory)

-}
module axiom.truncation where

open import prelude

private variable ℓ ℓ' : Level

------------------------------------------------------------------------------------------
-- Propositional truncation
------------------------------------------------------------------------------------------

postulate
  ∥_∥ : Type ℓ → Type ℓ

module _ {A : Type ℓ} where
  postulate
    ∣_∣ : A → ∥ A ∥

    trunc : isProp ∥ A ∥

    ∥∥-rec : (P : Type ℓ') (f : A → P) (p : ∀ a b → f a ≡ f b)
      → ∥ A ∥ → P

    ∥∥-rec-β : ∀ (P : Type ℓ') f p a → ∥∥-rec P f p ∣ a ∣ ≡ f a

    ∥∥-elim : (P : ∥ A ∥ → Type ℓ')
      (f : (a : A) → P ∣ a ∣)
      (p : ∀ a b → subst P (trunc ∣ a ∣ ∣ b ∣) (f a) ≡ f b)
      → (t : ∥ A ∥) → P t

    ∥∥-elim-β : ∀ (P : ∥ A ∥ → Type ℓ') f p a
      → ∥∥-elim P f p ∣ a ∣ ≡ f a

    {-# REWRITE ∥∥-rec-β ∥∥-elim-β #-}

trunc' : {A : Type ℓ} {x y : ∥ A ∥} → x ≡ y
trunc' = trunc _ _

∥_∥` : {A : Type ℓ} {B : Type ℓ'} → (A → B) → ∥ A ∥ → ∥ B ∥
∥_∥` f = ∥∥-rec _ (∣_∣ ∘ f) (λ _ _ → trunc')
