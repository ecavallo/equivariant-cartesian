{-

Notation and basic properties of functions.

-}
module basic.function where

open import basic.prelude

private variable
  ℓ ℓ' ℓ'' : Level

--↓ Alternate notation for Π-types.

Π : (A : Type ℓ) → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Π A B = (a : _) → B a

--↓ Identity function.

id : {A : Type ℓ} → A → A
id a = a

--↓ Constant function.

cst : {A : Type ℓ} {B : Type ℓ''} → B → A → B
cst b a = b

--↓ Composition of (dependent) functions.

_∘_ : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)

infixr 5 _∘_

--↓ Function application.

_$_ : {A : Type ℓ} {B : A → Type ℓ'} → ((a : A) → B a) → (a : A) → B a
f $ a = f a

infixr 5 _$_

--↓ Infix notation for "flip".

_⦅–⦆_ : {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
  → ((a : A) (b : B) → C a b) → (b : B) (a : A) → C a b
(f ⦅–⦆ b) a = f a b
