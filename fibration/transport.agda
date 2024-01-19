{-

Transport

-}
module fibration.transport where

open import basic
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ ℓ' : Level
  Γ : Type ℓ

--↓ Open box corresponding to transport (i.e. with an empty tube)

transpBox : {S : Shape} (A : ⟨ S ⟩ → Type ℓ) (r : ⟨ S ⟩) (a : A r) → OpenBox S A r
transpBox A r a .cof = ⊥
transpBox A r a .tube _ ()
transpBox A r a .cap .out = a
transpBox A r a .cap .out≡ ()

--↓ Type of transport structures on a family.

record TranspStr {Γ : Type ℓ} (A : Γ → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    --↓ We have a transport operation on every shape.

    lift : (S : Shape) (γ : Γ ^ S) (r : ⟨ S ⟩) (a : A (γ r)) (s : ⟨ S ⟩) → A (γ s)

    cap≡ : (S : Shape) (γ : Γ ^ S) (r : ⟨ S ⟩) (a : A (γ r)) → lift S γ r a r ≡ a

    --↓ The transport structures satisfy the equivariance condition.

    vary : ∀ S T (σ : ShapeHom S T)
      (γ : Γ ^ T) (r : ⟨ S ⟩) (a : A (γ (⟪ σ ⟫ r))) (s : ⟨ S ⟩)
      → lift T γ (⟪ σ ⟫ r) a (⟪ σ ⟫ s) ≡ lift S (γ ∘ ⟪ σ ⟫) r a s

open TranspStr public

fibStrToTranspStr : {A : Γ → Type ℓ} → FibStr A → TranspStr A
fibStrToTranspStr {A = A} α .lift S γ r a s =
  α .lift S γ r (transpBox (A ∘ γ) r a) .fill s .out
fibStrToTranspStr {A = A} α .cap≡ S γ r a =
  α .lift S γ r (transpBox (A ∘ γ) r a) .cap≡
fibStrToTranspStr {A = A} α .vary S T σ γ r a s =
  α .vary S T σ γ r (transpBox (A ∘ γ) (⟪ σ ⟫ r) a) s
  ∙ cong (λ box → α .lift S (γ ∘ ⟪ σ ⟫) r box .fill s .out) (boxExt refl (λ _ ()) refl)

fibTranspStr : (A : Γ ⊢ᶠType ℓ) → TranspStr ∣ A ∣
fibTranspStr A = fibStrToTranspStr (A .snd)
