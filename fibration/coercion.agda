{-

Coercion

-}
{-# OPTIONS --rewriting #-}
module fibration.coercion where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ : Level

module _ (S : Shape) (r : ⟨ S ⟩) (A : Fib ℓ ⟨ S ⟩) (a : A .fst r) where

  coerceBox : OpenBox S r (A .fst)
  coerceBox .cof = ⊥
  coerceBox .tube e _ = 𝟘-rec e
  coerceBox .cap .out = a
  coerceBox .cap .out≡ ()

  coerceFiller : Filler coerceBox
  coerceFiller = A .snd .lift S r id coerceBox

  coerce : (s : ⟨ S ⟩) → A .fst s
  coerce s = coerceFiller .fill s .out

  coerceCap : coerce r ≡ a
  coerceCap = coerceFiller .cap≡

module _ {S T : Shape} (σ : ShapeHom S T)
  (r : ⟨ S ⟩) (A : Fib ℓ ⟨ T ⟩) (a : A .fst (⟪ σ ⟫ r))
  where

  coerceVary : (s : ⟨ S ⟩) →
    coerce T (⟪ σ ⟫ r) A a (⟪ σ ⟫ s) ≡ coerce S r (A ∘ᶠ ⟪ σ ⟫) a s
  coerceVary s =
    A .snd .vary S T σ r id (coerceBox T _ A a) s
    ∙ cong (λ box → A .snd .lift S r ⟪ σ ⟫ box .fill s .out) (boxExt refl (λ ()) refl)
