{-

  Properties of fibrant replacement.

-}
module fibration.fibrant-replacement where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration

private variable
  ℓ ℓ' ℓ'' : Level
  Γ Δ : Type ℓ

--↓ The fibrant replacement of a map A → Γ is a fibration over Γ

FibReplaceFibStr : {A : Type ℓ} (π : A → Γ) → FibStr (FibReplace π)
FibReplaceFibStr π .lift S p r box =
  fitsPartialToFiller total
  where
  total : ∀ s → FibReplace π (p s) [ box .cof ∨ S ∋ r ≈ s ↦ boxToPartial box s ]
  total s .out = liftfr π S p r (box .cof) (boxToPartial box) s
  total s .out≡ = matchfr π S p r (box .cof) (boxToPartial box) s
FibReplaceFibStr π .vary S T σ p r box s =
  varyfr π S T σ p r (box .cof) (boxToPartial box) s
  ∙ cong
      (λ box' → liftfr π S (p ∘ ⟪ σ ⟫) r (box .cof) box' s)
      (funExt λ i → funExt λ u → reshapeBoxToPartial σ box i ((id ∨` cong ⟪ σ ⟫) u) u)

FibReplaceᶠ : {Γ : Type ℓ} {A : Type ℓ'} (π : A → Γ) → Γ ⊢ᶠType (ℓ ⊔ ℓ')
FibReplaceᶠ π .fst = FibReplace π
FibReplaceᶠ π .snd = FibReplaceFibStr π

--↓ Given a (fibrant) type family P over the fibrant replacement of a map π : A → Γ,
--↓ a section of the pullback of P to A induces a section of P.

FibReplace-elimFib :
  {A : Type ℓ} (π : A → Γ)
  (P : Γ ▷ˣ FibReplace π ⊢ᶠType ℓ')
  (infr* : (a : A) → P $ᶠ (π a , infr π a))
  → (γ : Γ) (t : FibReplace π γ) → P $ᶠ (γ , t)
FibReplace-elimFib π P infr* =
  FibReplace-elim π
    infr*
    (λ S γ r φ part part* s →
      fibLiftPartial P S (γ ,, liftfr π S γ r φ part) r φ (fixPart γ part*) s .out)
    (λ S γ r φ part part* s →
      fibLiftPartial P S (γ ,, liftfr π S γ r φ part) r φ (fixPart γ part*) s .out≡)
    (λ S T σ γ r φ part part* s →
      fibVaryPartial P σ (γ ,, liftfr π T γ (⟪ σ ⟫ r) φ part) r φ (fixPart γ part*) s
      ∙ cong (λ part' → fibLiftPartial P S _ r φ part' s .out) (reshapeFixPart σ γ part*))
  where
  fixPart : ∀ {S} γ {r} {φ} {part}
    → ((i : ⟨ S ⟩) (u : [ φ ∨ S ∋ r ≈ i ]) → P $ᶠ (γ i , part i u))
    → (i : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ i ] → P $ᶠ (γ i , liftfr π S γ r φ part i)
  fixPart γ part* i u =
    subst (∣ P ∣ ∘ (γ i ,_)) (matchfr π _ γ _ _ _ i u) (part* i u)

  reshapeFixPart : ∀ {S T} (σ : Shape[ S , T ]) γ {r} {φ}
    {part : (i : ⟨ T ⟩) → [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ i ] → _}
    (part* : (i : ⟨ T ⟩) (u : [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ i ]) → P $ᶠ (γ i , part i u))
    → reshapePartial σ (fixPart γ part*) ≡ fixPart (γ ∘ ⟪ σ ⟫) (reshapePartial σ part*)
  reshapeFixPart σ γ part* =
      funExt λ i →
      funExt λ u →
      cong (subst (∣ P ∣ ∘ (γ (⟪ σ ⟫ i) ,_)) ⦅–⦆ (reshapePartial σ part* i u)) uip'

--↓ Non-recursive eliminator for the fibrant replacement: a map over Γ from π : A → Γ into
--↓ a fibration induces a map over Γ from its fibrant replacement.

FibReplace-recFib :
  {A : Type ℓ} (π : A → Γ)
  (P : Γ ⊢ᶠType ℓ')
  (infr* : (a : A) → P $ᶠ π a)
  → (γ : Γ) → FibReplace π γ → P $ᶠ γ
FibReplace-recFib π P infr* =
  FibReplace-elimFib π (P ∘ᶠ 𝒑) infr*
