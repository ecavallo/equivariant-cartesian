{-

  Fibrant replacement as a map from the universe of global types to the universe of fibrations.

-}
module universe.fibrant-replacement where

open import basic
open import internal-extensional-type-theory
open import axiom
open import fibration.fibration
open import fibration.fibrant-replacement

open import universe.core
open import universe.fibrant

--↓ Definition of the fibrant replacement. Note that because encode is a flat-modal
--↓ function, Replaceᵁ can only be applied to flat-modal (i.e. global) types.

Replaceᵁ : ∀ {@♭ ℓ} → @♭ Type ℓ → 𝑼 ℓ
Replaceᵁ A = encode (FibReplaceᶠ (λ (a : A) → tt)) tt
