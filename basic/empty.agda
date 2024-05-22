{-

Empty type and negation in the ambient type theory.

-}
module basic.empty where

open import basic.prelude

private variable
  ℓ : Level

--↓ Empty type.

data 𝟘 : Type where

--↓ Elimination from the empty type.

𝟘-elim : {A : 𝟘 → Type ℓ} → (v : 𝟘) → A v
𝟘-elim ()

--↓ Non-dependent elimination from the empty type.

𝟘-rec : {A : Type ℓ} → 𝟘 → A
𝟘-rec ()

--↓ Negation of a type.

¬_ : Type ℓ → Type ℓ
¬ A = A → 𝟘
