{-

Function extensionality axiom and basic consequences

-}
module axiom.funext where

open import basic.prelude

private variable ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------------------------
-- Function extensionality
------------------------------------------------------------------------------------------

postulate
  funExt : {A : Type ℓ} {B : A → Type ℓ'} {f₀ f₁ : (a : A) → B a}
    → ((a : A) → f₀ a ≡ f₁ a) → f₀ ≡ f₁

funExt' : {A : Type ℓ} {B : A → Type ℓ'} {f₀ f₁ : (a : A) → B a}
  → ({a : A} → f₀ a ≡ f₁ a) → f₀ ≡ f₁
funExt' p = funExt λ _ → p

------------------------------------------------------------------------------------------
-- Function extensionality for flat-modal functions
------------------------------------------------------------------------------------------

postulate
  funExt♭ : {@♭ ℓ : Level} {ℓ' : Level}
     {@♭ A : Type ℓ} {B : @♭ A → Type ℓ'}
     {f₀ f₁ : (@♭ a : A) → B a}
     → ((@♭ a : A) → f₀ a ≡ f₁ a) → f₀ ≡ f₁

funExt♭' : {@♭ ℓ : Level} {ℓ' : Level}
   {@♭ A : Type ℓ} {B : @♭ A → Type ℓ'}
   {f₀ f₁ : (@♭ a : A) → B a}
   → ({@♭ a : A} → f₀ a ≡ f₁ a) → f₀ ≡ f₁
funExt♭' h = funExt♭ λ _ → h
