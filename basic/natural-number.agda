{-

Natural numbers of the ambient type theory.
We import Agda's built-in natural number datatype.

-}
module basic.natural-number where

open import basic.prelude
open import basic.unit

open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.FromNat public using (Number ; fromNat)
