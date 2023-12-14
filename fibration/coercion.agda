{-

Coercion

-}
module fibration.coercion where

open import prelude
open import axiom
open import cofibration
open import fibration.fibration

private variable ℓ : Level

module Coerce (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ ⊢ᶠType ℓ) (a : ∣ A ∣ r) where

  box : OpenBox S r ∣ A ∣
  box .cof = ⊥
  box .tube _ = 𝟘-rec
  box .cap .out = a
  box .cap .out≡ ()

  opaque
    filler : Filler box
    filler = A .snd .lift S r id box

  coerce : (s : ⟨ S ⟩) → A $ᶠ s
  coerce s = filler .fill s .out

  open Filler filler public using (cap≡)

module _ {S T : Shape} (σ : ShapeHom S T)
  (r : ⟨ S ⟩) (A : ⟨ T ⟩ ⊢ᶠType ℓ) (a : A $ᶠ ⟪ σ ⟫ r)
  where

  private
    module S = Coerce S r (A ∘ᶠ ⟪ σ ⟫) a
    module T = Coerce T (⟪ σ ⟫ r) A a

  opaque
    unfolding Coerce.filler
    coerceVary : (s : ⟨ S ⟩) → T.coerce (⟪ σ ⟫ s) ≡ S.coerce s
    coerceVary s =
      A .snd .vary S T σ r id T.box s
      ∙ cong (λ box → A .snd .lift S r ⟪ σ ⟫ box .fill s .out) (boxExt refl (λ _ ()) refl)
