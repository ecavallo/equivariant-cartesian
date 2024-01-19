{-

Transposrt

-}
module fibration.transport where

open import basic
open import axiom
open import cofibration
open import fibration.fibration

private variable ℓ : Level

module Transp (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ ⊢ᶠType ℓ) (a : ∣ A ∣ r) where

  box : OpenBox S ∣ A ∣ r
  box .cof = ⊥
  box .tube _ = 𝟘-rec
  box .cap .out = a
  box .cap .out≡ ()

  opaque
    filler : Filler box
    filler = A .snd .lift S id r box

  transp : (s : ⟨ S ⟩) → A $ᶠ s
  transp s = filler .fill s .out

  open Filler filler public using (cap≡)

module _ {S T : Shape} (σ : ShapeHom S T)
  (r : ⟨ S ⟩) (A : ⟨ T ⟩ ⊢ᶠType ℓ) (a : A $ᶠ ⟪ σ ⟫ r)
  where

  private
    module S = Transp S r (A ∘ᶠ ⟪ σ ⟫) a
    module T = Transp T (⟪ σ ⟫ r) A a

  opaque
    unfolding Transp.filler
    transpVary : (s : ⟨ S ⟩) → T.transp (⟪ σ ⟫ s) ≡ S.transp s
    transpVary s =
      A .snd .vary S T σ id r T.box s
      ∙ cong (λ box → A .snd .lift S ⟪ σ ⟫ r box .fill s .out) (boxExt refl (λ _ ()) refl)
