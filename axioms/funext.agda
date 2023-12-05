{-

Function extensionality axiom and basic consequences

-}
module axioms.funext where

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

funExt♭ : {@♭ ℓ : Level} {ℓ' : Level}
   {@♭ A : Type ℓ} {B : @♭ A → Type ℓ'}
   {f g : (@♭ a : A) → B a}
   → ((@♭ a : A) → f a ≡ g a) → f ≡ g
funExt♭ {ℓ} {ℓ'} {A} {B} {f} {g} h =
  cong (λ k (@♭ a) → k (in♭ a)) (funExt h')
  where
  B' : ♭ A → Type ℓ'
  B' (in♭ a) = B a

  f' g' : (a : ♭ A) → B' a
  f' (in♭ a) = f a
  g' (in♭ a) = g a

  h' : (a : ♭ A) → f' a ≡ g' a
  h' (in♭ a) = h a

funExt♭' : {@♭ ℓ : Level} {ℓ' : Level}
   {@♭ A : Type ℓ} {B : @♭ A → Type ℓ'}
   {f g : (@♭ a : A) → B a}
   → ({@♭ a : A} → f a ≡ g a) → f ≡ g
funExt♭' h = funExt♭ λ _ → h
