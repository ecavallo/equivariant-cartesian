{-

  Natural numbers.
  We import Agda's builtin natural number datatype.

-}
module basic.natural-number where

open import basic.prelude
open import basic.unit

open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.FromNat public using (Number ; fromNat)
