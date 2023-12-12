{-

Function extensionality axiom and basic consequences

-}
module axiom.funext where

open import prelude

private variable ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------------------------
-- Function extensionality
------------------------------------------------------------------------------------------

postulate
  funExt : {A : Type ℓ} {B : A → Type ℓ'} {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a) → f ≡ g

funExt' : {A : Type ℓ} {B : A → Type ℓ'} {f g : (a : A) → B a}
  → ({a : A} → f a ≡ g a) → f ≡ g
funExt' p = funExt λ _ → p

funExtDepCod : {A : Type ℓ} {B : Type ℓ'} {C : A → Type ℓ''}
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {f₀ : B → C a₀} {f₁ : B → C a₁}
  → (∀ b → subst C p (f₀ b) ≡ f₁ b)
  → subst (λ a → B → C a) p f₀ ≡ f₁
funExtDepCod refl = funExt

------------------------------------------------------------------------------------------
-- Function extensionality for flat-modal functions
------------------------------------------------------------------------------------------

postulate
  funExt♭ : {@♭ ℓ : Level} {ℓ' : Level}
     {@♭ A : Type ℓ} {B : @♭ A → Type ℓ'}
     {f g : (@♭ a : A) → B a}
     → ((@♭ a : A) → f a ≡ g a) → f ≡ g

funExt♭' : {@♭ ℓ : Level} {ℓ' : Level}
   {@♭ A : Type ℓ} {B : @♭ A → Type ℓ'}
   {f g : (@♭ a : A) → B a}
   → ({@♭ a : A} → f a ≡ g a) → f ≡ g
funExt♭' h = funExt♭ λ _ → h
