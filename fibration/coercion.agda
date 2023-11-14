{-

Coercion

-}
{-# OPTIONS --rewriting #-}
module fibration.coercion where

open import prelude
open import axioms
open import fibration.fibration

module _ {ℓ} (S : Shape) (r : ⟨ S ⟩) {A : ⟨ S ⟩ → Set ℓ} (α : isFib A) (a : A r)where

  coerceBox : OpenBox S r A
  coerceBox .cof = ⊥
  coerceBox .tube e _ = ∅-rec e
  coerceBox .cap .fst = a
  coerceBox .cap .snd ()

  coerceFiller : Filler coerceBox
  coerceFiller = α .lift S r id coerceBox

  coerce : (s : ⟨ S ⟩) → A s
  coerce s = coerceFiller .fill s .fst

  coerceCap : coerce r ≡ a
  coerceCap = coerceFiller .cap≡

module _ {ℓ} (S T : Shape) (σ : ShapeHom S T)
  (r : ⟨ S ⟩) {A : ⟨ T ⟩ → Set ℓ} (α : isFib A) (a : A (⟪ σ ⟫ r))
  where

  coerceVary : (s : ⟨ S ⟩) → coerce T (⟪ σ ⟫ r) α a (⟪ σ ⟫ s) ≡ coerce S r (reindex A α ⟪ σ ⟫) a s
  coerceVary s =
    α .vary S T σ r id (coerceBox T _ α a) s
    ∙ cong (λ box → α .lift S r ⟪ σ ⟫ box .fill s .fst) (boxExt refl (λ ()) refl)
