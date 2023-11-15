{-

Function extensionality axiom and basic consequences

-}
{-# OPTIONS --rewriting #-}
module axioms.funext where

open import prelude

private variable ℓ ℓ' ℓ'' : Level

----------------------------------------------------------------------
-- Function extensionality
----------------------------------------------------------------------

postulate
  funext :
     {A : Set ℓ}
     {B : A → Set ℓ'}
     {f g : (x : A) → B x}
     → ----------------------------
     ((x : A) → f x ≡ g x) → f ≡ g

funextDepCod : {A : Set ℓ} {B : Set ℓ'} {C : A → Set ℓ''}
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {f₀ : B → C a₀} {f₁ : B → C a₁}
  → (∀ b → subst C p (f₀ b) ≡ f₁ b)
  → subst (λ a → B → C a) p f₀ ≡ f₁
funextDepCod refl = funext

funext♭ :
   {@♭ ℓ : Level} {ℓ' : Level}
   {@♭ A : Set ℓ}
   {B : @♭ A → Set ℓ'}
   {f g : (@♭ x : A) → B x}
   → ----------------------------
   ((@♭ x : A) → f x ≡ g x) → f ≡ g
funext♭ {ℓ} {ℓ'} {A} {B} {f} {g} h =
  cong (λ k (@♭ a) → k (in♭ a)) (funext h')
  where
  B' : ♭ A → Set ℓ'
  B' (in♭ a) = B a

  f' g' : (a : ♭ A) → B' a
  f' (in♭ a) = f a
  g' (in♭ a) = g a

  h' : (a : ♭ A) → f' a ≡ g' a
  h' (in♭ a) = h a
