{-

Definition of isomorphism in the ambient type theory (with inverses up to strict
equality).

-}
module basic.isomorphism where

open import basic.prelude
open import basic.equality

private variable
  ℓ ℓ' : Level

infix 4 _≅_

--↓ Definition of isomorphism.

record _≅_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
 field
  to   : A → B
  from : B → A
  inv₁ : ∀ a → from (to a) ≡ a
  inv₂ : ∀ b → to (from b) ≡ b

open _≅_ public
