{-

Function extensionality

-}
{-# OPTIONS --rewriting #-}
module axioms.funext where

open import prelude

----------------------------------------------------------------------
-- Function extensionality
----------------------------------------------------------------------

postulate
  funext :
     {ℓ  ℓ' : Level}
     {A : Set ℓ}
     {B : A → Set ℓ'}
     {f g : (x : A) → B x}
     → ----------------------------
     ((x : A) → f x ≡ g x) → f ≡ g

funextDepCod : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : A → Set ℓ''}
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {f₀ : B → C a₀} {f₁ : B → C a₁}
  → (∀ b → subst C p (f₀ b) ≡ f₁ b)
  → subst (λ a → B → C a) p f₀ ≡ f₁
funextDepCod refl = funext
