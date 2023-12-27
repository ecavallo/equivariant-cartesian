{-

  Coproducts.

-}
module basic.coproduct where

open import basic.prelude
open import basic.function

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

data _⊎_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 3 _⊎_

--↓ Elimination from a coproduct.

⊎-elim : {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''}
  → ((a : A) → C (inl a))
  → ((b : B) → C (inr b))
  → (z : A ⊎ B) → C z
⊎-elim f g (inl a) = f a
⊎-elim f g (inr b) = g b

[_∣_] = ⊎-elim

--↓ Functoriality of coproducts.

_⊎`_ : {A : Type ℓ} {A' : Type ℓ'} {B : Type ℓ''} {B' : Type ℓ'''}
  → (A → A') → (B → B') → (A ⊎ B) → (A' ⊎ B')
(f ⊎` g) = [ inl ∘ f ∣ inr ∘ g ]

--↓ Codiagonal function.

∇ : {A : Type ℓ} → A ⊎ A → A
∇ = [ id ∣ id ]
