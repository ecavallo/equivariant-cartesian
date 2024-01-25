{-

Absolute basics:
- universe levels for the ambient type theory;
- definition of equality.

-}
module basic.prelude where

open import Agda.Primitive public renaming (Set to Type)

data _≡_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
  instance
    refl : a ≡ a

infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}
