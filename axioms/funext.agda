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
     {A : Type ℓ}
     {B : A → Type ℓ'}
     {f g : (x : A) → B x}
     → ----------------------------
     ((x : A) → f x ≡ g x) → f ≡ g

funextDepCod : {A : Type ℓ} {B : Type ℓ'} {C : A → Type ℓ''}
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {f₀ : B → C a₀} {f₁ : B → C a₁}
  → (∀ b → subst C p (f₀ b) ≡ f₁ b)
  → subst (λ a → B → C a) p f₀ ≡ f₁
funextDepCod refl = funext

funext♭ :
   {@♭ ℓ : Level} {ℓ' : Level}
   {@♭ A : Type ℓ}
   {B : @♭ A → Type ℓ'}
   {f g : (@♭ x : A) → B x}
   → ----------------------------
   ((@♭ x : A) → f x ≡ g x) → f ≡ g
funext♭ {ℓ} {ℓ'} {A} {B} {f} {g} h =
  cong (λ k (@♭ a) → k (in♭ a)) (funext h')
  where
  B' : ♭ A → Type ℓ'
  B' (in♭ a) = B a

  f' g' : (a : ♭ A) → B' a
  f' (in♭ a) = f a
  g' (in♭ a) = g a

  h' : (a : ♭ A) → f' a ≡ g' a
  h' (in♭ a) = h a
