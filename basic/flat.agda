{-

Properties of flat-modal functions.

-}
module basic.flat where

open import basic.prelude
open import basic.equality

private variable
  ℓ ℓ' : Level

--↓ Application of a flat-modal function.

_$♭_ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} {B : A → Type ℓ'} → ((@♭ a : A) → B a) → (@♭ a : A) → B a
f $♭ a = f a

infixr 5 _$♭_

--↓ Substitution for flat-modal families.

--↓ Congruence for flat-modal functions.

cong♭ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} {B : Type ℓ'}
  (f : @♭ A → B) {@♭ a₀ a₁ : A} (@♭ p : a₀ ≡ a₁) → f a₀ ≡ f a₁
cong♭ _ refl = refl

congdep♭ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} {B : A → Type ℓ'}
  (f : (@♭ a : A) → B a) {@♭ a₀ a₁ : A} (@♭ p : a₀ ≡ a₁) → subst B p (f a₀) ≡ f a₁
congdep♭ _ refl = refl

--↓ Congruence of function application for flat-model functions.

cong$♭ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} {B : A → Type ℓ'}
  {f g : (@♭ a : A) → B a}
  {@♭ a : A} (p : f ≡ g) → f a ≡ g a
cong$♭ p = cong (_$♭ _) p
