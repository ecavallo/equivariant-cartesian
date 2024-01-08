{-

Axioms specifying that each shape is tiny.

-}
module axiom.tiny where

open import basic
open import axiom.shape

infixr 4 _√_

postulate
  _√_ : ∀ {@♭ ℓ} (@♭ S : Shape) (@♭ A : Type ℓ) → Type ℓ

module √Axioms (@♭ S : Shape) where

  module _ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'} where

    postulate
      --↓ Transposition from left to right.

      R : @♭ (A ^ S → B) → (A → S √ B)

      --↓ Transposition from right to left.

      L : @♭ (A → S √ B) → (A ^ S → B)

      --↓ Right and left transposition are mutually inverse.

      LR : (@♭ f : A ^ S → B) → L (R f) ≡ f
      RL : (@♭ g : A → S √ B) → R (L g) ≡ g

    {-# REWRITE LR RL #-}

  postulate
    --↓ One-sided naturality of right transposition.

    R^ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
      (@♭ h : A → A') (@♭ f : A' ^ S → B)
      → R (f ∘ h `^ S) ≡ R f ∘ h
