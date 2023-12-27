{-

   Empty type and negation.

-}
module basic.empty where

open import basic.prelude

private variable
  ℓ : Level

data 𝟘 : Type where

𝟘-elim : {A : 𝟘 → Type ℓ} → (v : 𝟘) → A v
𝟘-elim ()

𝟘-rec : {A : Type ℓ} → 𝟘 → A
𝟘-rec ()

¬_ : Type ℓ → Type ℓ
¬ A = A → 𝟘
