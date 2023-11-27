{-

Coercion

-}
{-# OPTIONS --rewriting #-}
module fibration.coercion where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ : Level

module _ (S : Shape) (r : ⟨ S ⟩) {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A) (a : A r) where

  coerceBox : OpenBox S r A
  coerceBox .cof = ⊥
  coerceBox .tube e _ = 𝟘-rec e
  coerceBox .cap .out = a
  coerceBox .cap .out≡ ()

  coerceFiller : Filler coerceBox
  coerceFiller = α .lift S r id coerceBox

  coerce : (s : ⟨ S ⟩) → A s
  coerce s = coerceFiller .fill s .out

  coerceCap : coerce r ≡ a
  coerceCap = coerceFiller .cap≡

module _ {S T : Shape} (σ : ShapeHom S T)
  (r : ⟨ S ⟩) {A : ⟨ T ⟩ → Type ℓ} (α : FibStr A) (a : A (⟪ σ ⟫ r))
  where

  coerceVary : (s : ⟨ S ⟩) →
    coerce T (⟪ σ ⟫ r) α a (⟪ σ ⟫ s) ≡ coerce S r (reindexFibStr α ⟪ σ ⟫) a s
  coerceVary s =
    α .vary S T σ r id (coerceBox T _ α a) s
    ∙ cong (λ box → α .lift S r ⟪ σ ⟫ box .fill s .out) (boxExt refl (λ ()) refl)
