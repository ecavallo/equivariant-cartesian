{-

Postulates a quotient inductive family for fibrant replacement of an internal family.

-}
module axioms.fibrant-replacement where

open import prelude
open import axioms.cofibration
open import axioms.funext
open import axioms.shape
open import axioms.truncation
open import fibration.fibration

private variable
  ℓ ℓ' : Level
  Γ : Type ℓ

--↓ Representation of open boxes as partial elements over a union.

PartBox : (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ → Type ℓ) (φ : Cof) → Type ℓ
PartBox S r A φ = ((i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → A i)

reshapePartBox : {S T : Shape} (σ : ShapeHom S T) {r : ⟨ S ⟩}
  {A : ⟨ T ⟩ → Type ℓ} (φ : Cof)
  → PartBox T (⟪ σ ⟫ r) A φ → PartBox S r (A ∘ ⟪ σ ⟫) φ
reshapePartBox σ φ part i =
  part (⟪ σ ⟫ i) ∘ ∥ id ⊎` cong ⟪ σ ⟫ ∥`

PartBoxᴰ : (S : Shape) (r : ⟨ S ⟩)
  {A : ⟨ S ⟩ → Type ℓ} (P : (s : ⟨ S ⟩) → A s → Type ℓ') (φ : Cof)
  → PartBox S r A φ → Type ℓ'
PartBoxᴰ S r P φ part =
  (i : ⟨ S ⟩) (u : [ φ ∨ S ∋ r ≈ i ]) → P i (part i u)

reshapePartBoxᴰ : {S T : Shape} (σ : ShapeHom S T) {r : ⟨ S ⟩}
  {A : ⟨ T ⟩ → Type ℓ} (P : (t : ⟨ T ⟩) → A t → Type ℓ') (φ : Cof)
  {part : PartBox T (⟪ σ ⟫ r) A φ}
  → PartBoxᴰ T (⟪ σ ⟫ r) P φ part
  → PartBoxᴰ S r (P ∘ ⟪ σ ⟫) φ (reshapePartBox σ φ part)
reshapePartBoxᴰ σ P φ partᴰ i =
  partᴰ (⟪ σ ⟫ i) ∘ ∥ id ⊎` cong ⟪ σ ⟫ ∥`

--↓ Postulates the fibrant replacement of a family of types.

postulate
  FibReplace : (Γ → Type ℓ) → Γ → Type ℓ

module _ {A : Γ → Type ℓ} where

  postulate
    --↓ Constructors for the fibrant replacement as an indexed quotient inductive type.

    --↓ There are two point constructors (inFR and the first component of fillFR), one for
    --↓ the map from A and one for filling open boxes. There are two equality constructors
    --↓ (the second component of fillFR and varyFR), one which states that fillFR fills
    --↓ the open box it is given and one which states that filling is equivariant.

    inFR : {γ : Γ} → A γ → FibReplace A γ
    fillFR : ∀ S r (p : ⟨ S ⟩ → Γ) φ (part : PartBox S r (FibReplace A ∘ p) φ)
      → ∀ s → FibReplace A (p s) [ φ ∨ S ∋ r ≈ s ↦ part s ]
    varyFR : ∀ {S T} (σ : ShapeHom S T) r p φ part s
      → fillFR T (⟪ σ ⟫ r) p φ part (⟪ σ ⟫ s) .out
        ≡ fillFR S r (p ∘ ⟪ σ ⟫) φ (reshapePartBox σ φ part) s .out

    --↓ Postulated dependent eliminator for the fibrant replacement.

    fibReplaceElim : {P : (γ : Γ) → FibReplace A γ → Type ℓ'}
      (inFRᴰ : ∀ γ a → P γ (inFR a))
      (fillFRᴰ : ∀ S r p φ part (partᴰ : PartBoxᴰ S r (P ∘ p) φ part) s
        → P (p s) (fillFR S r p φ part s .out)
          [ u ∈ φ ∨ S ∋ r ≈ s ↦
            subst (P (p s)) (fillFR S r p φ part s .out≡ u) (partᴰ s u) ])
      (varyFRᴰ : ∀ {S T} (σ : ShapeHom S T) r p φ part partᴰ s
         → subst (P _) (varyFR σ r p φ part s) (fillFRᴰ T _ _ _ _ partᴰ _ .out)
           ≡ fillFRᴰ S _ _ _ _ (reshapePartBoxᴰ σ (P ∘ p) φ partᴰ) _ .out)
      (γ : Γ) (f : FibReplace A γ) → P γ f

  --↓ Non-dependent recursor derived from the dependent eliminator

  fibReplaceRec : {B : (γ : Γ) → Type ℓ'}
    (inFR* : ∀ γ → A γ → B γ)
    (fillFR* : ∀ S r p φ
      (part : PartBox S r (FibReplace A ∘ p) φ)
      (part* : PartBox S r (B ∘ p) φ)
      → ∀ s → B (p s) [ φ ∨ S ∋ r ≈ s ↦ part* s ])
    (varyFR* : ∀ {S T} (σ : ShapeHom S T) r p φ
      (part : PartBox T (⟪ σ ⟫ r) (FibReplace A ∘ p) φ)
      (part* : PartBox T (⟪ σ ⟫ r) (B ∘ p) φ)
      → ∀ s
      → fillFR* T _ _ φ part part* (⟪ σ ⟫ s) .out
        ≡ fillFR* S r _ φ (reshapePartBox σ φ part) (reshapePartBox σ φ part*) s .out)
    (γ : Γ) → FibReplace A γ → B γ
  fibReplaceRec {B = B} inFR* fillFR* varyFR* =
    fibReplaceElim inFR* fillFRᴰ
      (λ σ r p φ part partᴰ s →
        substConst (varyFR σ r p φ part s) _ ∙ varyFR* σ r p φ part partᴰ s)
    where
    fillFRᴰ : ∀ S r p φ part (part* : PartBox S r (B ∘ p) φ) s
      → B (p s)
        [ u ∈ _ ↦ subst (cst (B (p s))) (fillFR S r p φ part s .out≡ u) (part* s u) ]
    fillFRᴰ S r p φ part part* s .out = fillFR* S r p φ part part* s .out
    fillFRᴰ S r p φ part part* s .out≡ u =
      substConst (fillFR S r p φ part s .out≡ u) _
      ∙ fillFR* S r p φ part part* s .out≡ u

  --↓ Elimination from the fibrant replacement into propositions.

  opaque
    fibReplaceElimProp : {P : (γ : Γ) → FibReplace A γ → Type ℓ'}
      (propP : ∀ γ f → isProp (P γ f))
      (inFRᴰ : ∀ γ a → P γ (inFR a))
      (fillFRᴰ : ∀ S r p φ part (partᴰ : PartBoxᴰ S r (P ∘ p) φ part) s
        → P (p s) (fillFR S r p φ part s .out))
      (γ : Γ) (f : FibReplace A γ) → P γ f
    fibReplaceElimProp propP inFRᴰ fillFRᴰ =
      fibReplaceElim inFRᴰ
        (λ S r p φ part part* s → λ where
          .out → fillFRᴰ S r p φ part part* s
          .out≡ u → propP _ _ _ _)
        (λ σ r p φ part partᴰ s → propP _ _ _ _)

--↓ Fibrancy structure on the fibrant replacement

FibReplaceFibStr : (A : Γ → Type ℓ) → FibStr (FibReplace A)
FibReplaceFibStr A .lift S r p box =
  fitsPartialToFiller (fillFR _ _ _ _ (boxToPartial box))
FibReplaceFibStr A .vary S T σ r p box s =
  varyFR σ r p (box .cof) (boxToPartial box) s
  ∙ cong
      (λ part → fillFR S r (p ∘ ⟪ σ ⟫) (box .cof) part s .out)
      (funExt λ i → funExt $
        ∨-elimEq (box .cof) (S ∋ r ≈ i) (λ _ → refl) (λ {refl → refl}))
