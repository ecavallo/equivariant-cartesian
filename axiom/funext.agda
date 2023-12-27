{-

Function extensionality axiom and basic consequences

-}
module axiom.funext where

open import basic.prelude
open import basic.equality

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
