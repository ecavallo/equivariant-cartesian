{-

Definition of (equivariant) transport structure on a family.
This is the special case of filling structure where the cofibration is empty.

-}
module fibration.transport where

open import basic
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ


--↓ Type of transport structures on a family.

record TranspStr {Γ : Type ℓ} (A : Γ → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    --↓ We have a transport operation for every shape.

    lift : (S : Shape) (γ : Γ ^ S) (r : ⟨ S ⟩) (a : A (γ r)) (s : ⟨ S ⟩) → A (γ s)

    cap≡ : (S : Shape) (γ : Γ ^ S) (r : ⟨ S ⟩) (a : A (γ r)) → lift S γ r a r ≡ a

    --↓ The transport structures must satisfy an equivariance condition.

    vary : ∀ S T (σ : Shape[ S , T ])
      (γ : Γ ^ T) (r : ⟨ S ⟩) (a : A (γ (⟪ σ ⟫ r))) (s : ⟨ S ⟩)
      → lift T γ (⟪ σ ⟫ r) a (⟪ σ ⟫ s) ≡ lift S (γ ∘ ⟪ σ ⟫) r a s

open TranspStr public

--↓ Reindexing of transport structures.

_∘ᵗˢ_ : {A : Γ → Type ℓ} (α : TranspStr A) (ρ : Δ → Γ) → TranspStr (A ∘ ρ)
(α ∘ᵗˢ ρ) .lift S γ = α .lift S (ρ ∘ γ)
(α ∘ᵗˢ ρ) .cap≡ S γ = α .cap≡ S (ρ ∘ γ)
(α ∘ᵗˢ ρ) .vary S T σ γ = α .vary S T σ (ρ ∘ γ)

--↓ Open box corresponding to transport (i.e. with an empty tube)

transpBox : {S : Shape} (A : ⟨ S ⟩ → Type ℓ) (r : ⟨ S ⟩) (a : A r) → OpenBox S A r
transpBox A r a .cof = ⊥
transpBox A r a .tube _ ()
transpBox A r a .cap .out = a
transpBox A r a .cap .out≡ ()

--↓ Any fibration structure can be restricted to a transport structure.

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

------------------------------------------------------------------------------------------
-- Given a transport structure on a family and a fibration structure on every fiber of the
-- family (a "homogeneous filling structure"), we can construct a fibration structure on
-- that family.
--
-- This would be used in an extension of the interpretation to include higher inductive
-- types.
------------------------------------------------------------------------------------------

FiberwiseFibStr : {Γ : Type ℓ} → (Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
FiberwiseFibStr A = ∀ γ → FibStr {Γ = 𝟙} (A ∘ cst γ)

module FromFiberwiseLift {S} {A : ⟨ S ⟩ → Type ℓ}
  (transp : TranspStr A)
  (hcomp : FiberwiseFibStr A)
  {r : ⟨ S ⟩} (box : OpenBox S A r)
  where
  module _ (s : ⟨ S ⟩) where
    fiberBox : OpenBox S (cst (A s)) r
    fiberBox .cof = box .cof
    fiberBox .tube i u = transp .lift S id i (box .tube i u) s
    fiberBox .cap .out = transp .lift S id r (box .cap .out) s
    fiberBox .cap .out≡ u = cong (transp .lift S id r ⦅–⦆ s) (box .cap .out≡ u)

    fiberFiller : Filler fiberBox
    fiberFiller = hcomp s .lift S _ r fiberBox

  opaque
    filler : Filler box
    filler .fill s .out = fiberFiller s .fill s .out
    filler .fill s .out≡ u =
      sym (transp .cap≡ S id s (box .tube s u))
      ∙ fiberFiller s .fill s .out≡ u
    filler .cap≡ =
      fiberFiller r .cap≡
      ∙ transp .cap≡ S id r (box .cap .out)

module FromFiberwiseVary {S T} (σ : Shape[ S , T ]) {A : ⟨ T ⟩ → Type ℓ}
  (transp : TranspStr A)
  (hcomp : FiberwiseFibStr A)
  {r : ⟨ S ⟩} (box : OpenBox T A (⟪ σ ⟫ r))
  where

  module T = FromFiberwiseLift transp hcomp box
  module S = FromFiberwiseLift (transp ∘ᵗˢ ⟪ σ ⟫) (hcomp ∘ ⟪ σ ⟫) (reshapeBox σ box)

  boxEq : ∀ s → reshapeBox σ (T.fiberBox (⟪ σ ⟫ s)) ≡ S.fiberBox s
  boxEq s =
    boxExt
      refl
        (λ i → diagonalCofElim (box .cof) λ u →
          transp .vary S T σ id i (box .tube (⟪ σ ⟫ i) u) s)
        (transp .vary S T σ id r (box .cap .out) s)

  opaque
    unfolding FromFiberwiseLift.filler
    eq : ∀ s → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
    eq s =
      hcomp (⟪ σ ⟫ s) .vary S T σ _ r (T.fiberBox (⟪ σ ⟫ s)) s
      ∙ cong (λ box' → hcomp (⟪ σ ⟫ s) .lift S _ r box' .fill s .out) (boxEq s)

transpAndFiberwiseToFibStr : {A : Γ → Type ℓ}
  → TranspStr A
  → FiberwiseFibStr A
  → FibStr A
transpAndFiberwiseToFibStr {A = A} transp hcomp .lift S γ r box =
  FromFiberwiseLift.filler (transp ∘ᵗˢ γ) (hcomp ∘ γ) box
transpAndFiberwiseToFibStr transp hcomp .vary S T σ γ r box s =
  FromFiberwiseVary.eq σ (transp ∘ᵗˢ γ) (hcomp ∘ γ) box s
