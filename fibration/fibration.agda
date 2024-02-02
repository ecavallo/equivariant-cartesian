{-

Defines fibration structures and fibrations.

-}
module fibration.fibration where

open import basic
open import internal-extensional-type-theory
open import axiom.cofibration
open import axiom.funext
open import axiom.shape
open import cofibration

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

infix  1 _⊢ᶠType_ _⊢ᶠ_
infixl 3 _▷ᶠ_
infixl 5 _∘ᶠˢ_ _∘ᶠ_ _$ᶠ_

------------------------------------------------------------------------------------------
-- Open boxes
------------------------------------------------------------------------------------------

--↓ The type of open boxes for a given shape S with the cap at a point r of S. An open box
--↓ consists of a cofibration, a partially defined element indexed by S (the "tube"), and
--↓ a total element (the "cap") agreeing with the tube at r.

record OpenBox (S : Shape) (A : ⟨ S ⟩ → Type ℓ) (r : ⟨ S ⟩) : Type ℓ
  where
  constructor makeBox
  field
    cof : Cof
    tube : (i : ⟨ S ⟩) → [ cof ] → A i
    cap : A r [ cof ↦ tube r ]

open OpenBox public

--↓ A shape homomorphism σ : S → T induces a map from T-boxes to S-boxes by
--↓ precomposition.

reshapeBox : ∀ {S T} (σ : Shape[ S , T ]) {r} {A : ⟨ T ⟩ → Type ℓ}
  → OpenBox T A (⟪ σ ⟫ r) → OpenBox S (A ∘ ⟪ σ ⟫) r
reshapeBox σ box .cof = box .cof
reshapeBox σ box .tube = box .tube ∘ ⟪ σ ⟫
reshapeBox σ box .cap = box .cap

--↓ Convenience function extending the tube of a box with another partial element.

addToTube : ∀ {S} {A : ⟨ S ⟩ → Type ℓ} {r}
  (box : OpenBox S A r)
  (φ : Cof)
  (t : (i : ⟨ S ⟩) → [ φ ] → A i [ box .cof ↦ box .tube i ])
  (matchCap : (v : [ φ ]) → t r v .out ≡ box .cap .out)
  → OpenBox S A r
addToTube box φ t matchCap .cof = box .cof ∨ φ
addToTube box φ t matchCap .tube i =
  ∨-rec (box .tube i) (out ∘ t i) (λ u v → t i v .out≡ u)
addToTube box φ t matchCap .cap .out = box .cap .out
addToTube box φ t matchCap .cap .out≡ =
  ∨-elimEq (box .cap .out≡) matchCap

------------------------------------------------------------------------------------------
-- Open boxes as partial elements.
------------------------------------------------------------------------------------------

--↓ An S-box with cofibration φ and cap at r can also be encoded as a family over
--↓ over s : S defined on φ ∨ r ≈ s. This representation is sometimes more convenient.

boxToPartial : ∀ {S} {A : ⟨ S ⟩ → Type ℓ} {r} (box : OpenBox S A r)
  (s : ⟨ S ⟩) → [ box .cof ∨ S ∋ r ≈ s ] → A s
boxToPartial box s =
  ∨-rec
    (box .tube s)
    (λ {refl → box .cap .out})
    (λ {u refl → box .cap .out≡ u})

partialToBox : ∀ {S} {A : ⟨ S ⟩ → Type ℓ} {r} (φ : Cof)
  → ((s : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ s ] → A s)
  → OpenBox S A r
partialToBox φ part .cof = φ
partialToBox φ part .tube i = part i ∘ ∨l
partialToBox φ part .cap .out = part _ (∨r refl)
partialToBox {S = S} {r = r} φ part .cap .out≡ u =
  cong (part _) (cofIsStrictProp' (φ ∨ S ∋ r ≈ r))

--↓ Action of shape homomorphisms on open boxes encoded as partial elements.

reshapePartial : ∀ {S T} (σ : Shape[ S , T ]) {r} {φ : Cof}
  {A : (j : ⟨ T ⟩) → [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ] → Type ℓ}
  → ((j : ⟨ T ⟩) (v : [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ j ]) → A j v)
  → ((i : ⟨ S ⟩) (u : [ φ ∨ S ∋ r ≈ i ]) → A (⟪ σ ⟫ i) ((id ∨` cong ⟪ σ ⟫) u))
reshapePartial σ part i = part (⟪ σ ⟫ i) ∘ (id ∨` cong ⟪ σ ⟫)

--↓ Reshaping open boxes commutes with the conversion from the record to the
--↓ partial-element representation.

opaque
  reshapeBoxToPartial : ∀ {S T} (σ : Shape[ S , T ]) {A : ⟨ T ⟩ → Type ℓ} {r}
    (box : OpenBox T A (⟪ σ ⟫ r))
    (s : ⟨ S ⟩)
    (v : [ box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s ])
    (u : [ box .cof ∨ S ∋ r ≈ s ])
    → boxToPartial box (⟪ σ ⟫ s) v ≡ boxToPartial (reshapeBox σ box) s u
  reshapeBoxToPartial {S = S} {T} σ {r = r} box s =
    takeOutCof (box .cof) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s) (S ∋ r ≈ s)
      (λ u → refl)
      (λ {refl refl → refl})

------------------------------------------------------------------------------------------
-- Solutions to individual lifting problems.
------------------------------------------------------------------------------------------

--↓ A filler for an S-box over A is a section of A that restricts to its tube and cap
--↓ where they are defined.

record Filler {S : Shape} {A : ⟨ S ⟩ → Type ℓ} {r : ⟨ S ⟩} (box : OpenBox S A r) : Type ℓ
  where
  constructor makeFiller
  field
    fill : (s : ⟨ S ⟩) → A s [ box .cof ↦ box .tube s ]
    cap≡ : fill r .out ≡ box .cap .out

open Filler public

--↓ A shape homomorphism σ : S → T induces a map from T-fillers to S-fillers by
--↓ precomposition.

reshapeFiller : {S T : Shape} (σ : Shape[ S , T ])
  {A : ⟨ T ⟩ → Type ℓ} {r : ⟨ S ⟩}
  {box : OpenBox T A (⟪ σ ⟫ r)}
  → Filler box
  → Filler (reshapeBox σ box)
reshapeFiller σ w .fill = w .fill ∘ ⟪ σ ⟫
reshapeFiller σ w .cap≡ = w .cap≡

--↓ A total section fitting an open box encoded as a partial section is the same
--↓ a filler for the open box encoded as a record.

fitsPartialToFiller : ∀ {S} {A : ⟨ S ⟩ → Type ℓ} {r} {box : OpenBox S A r}
  → ((s : ⟨ S ⟩) → A s [ box .cof ∨ S ∋ r ≈ s ↦ boxToPartial box s ])
  → Filler box
fitsPartialToFiller total .fill s = narrow (total s) ∨l
fitsPartialToFiller total .cap≡ = sym (total _ .out≡ (∨r refl))

fillerToFitsPartial : ∀ {S} {A : ⟨ S ⟩ → Type ℓ} {r} {box : OpenBox S A r}
  → Filler box
  → ((s : ⟨ S ⟩) → A s [ box .cof ∨ S ∋ r ≈ s ↦ boxToPartial box s ])
fillerToFitsPartial filler s .out = filler .fill s .out
fillerToFitsPartial filler s .out≡ =
  ∨-elimEq (filler .fill s .out≡) (λ {refl → sym (filler .cap≡)})

------------------------------------------------------------------------------------------
-- Equivariant fibrations.
------------------------------------------------------------------------------------------

--↓ Type of operations filling open boxes over a given shape-indexed family.

LocalFillStr : (S : Shape) (A : ⟨ S ⟩ → Type ℓ) → Type ℓ
LocalFillStr S A = ∀ r (box : OpenBox S A r) → Filler box

--↓ A filling structure on a family consists of a local filling structure for every
--↓ reindexing of the family over a shape. This would be the definition of fibration in
--↓ a "non-equivariant fibration" model.

FillStr : (S : Shape) {Γ : Type ℓ} (A : Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
FillStr S {Γ} A = (γ : Γ ^ S) → LocalFillStr S (A ∘ γ)

--↓ The equivariance condition on local filling structures associated to a shape
--↓ homomorphism σ : S → T. Filling an open box over T and then composing with σ should be
--↓ the same as composing the box with σ and then filling over S.

LocalEquivariance : {S T : Shape} (σ : Shape[ S , T ]) {A : ⟨ T ⟩ → Type ℓ}
  → LocalFillStr T A → LocalFillStr S (A ∘ ⟪ σ ⟫) → Type ℓ
LocalEquivariance σ liftT liftS =
  ∀ r box s →
  reshapeFiller σ (liftT (⟪ σ ⟫ r) box) .fill s .out
  ≡ liftS r (reshapeBox σ box) .fill s .out

Equivariance : {S T : Shape} (σ : Shape[ S , T ]) {Γ : Type ℓ} (A : Γ → Type ℓ')
  → FillStr T A → FillStr S A → Type (ℓ ⊔ ℓ')
Equivariance {T = T} σ {Γ} A fillT fillS =
  (γ : Γ ^ T) → LocalEquivariance σ (fillT γ) (fillS (γ ∘ ⟪ σ ⟫))

--↓ Definition of an equivariant fibration structure.

record FibStr {Γ : Type ℓ} (A : Γ → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor makeFib
  field
    --↓ We have a filling structure for every shape.

    lift : (S : Shape) → FillStr S A

    --↓ The filling structures satisfy the equivariance condition.

    vary : ∀ S T (σ : Shape[ S , T ]) → Equivariance σ A (lift T) (lift S)

open FibStr public

--↓ Fibrant type judgment.

_⊢ᶠType_ : (Γ : Type ℓ) (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Γ ⊢ᶠType ℓ' = Σ (Γ → Type ℓ') FibStr

--↓ Convenient and/or suggestive notation for accessing the underlying family of a fibrant
--↓ type and evaluating the family at some instantiation of the context (i.e., taking some
--↓ fiber).

∣_∣ : (Γ ⊢ᶠType ℓ) → (Γ → Type ℓ)
∣ A ∣ = A .fst

_$ᶠ_ : (Γ ⊢ᶠType ℓ) → Γ → Type ℓ
A $ᶠ γ = ∣ A ∣ γ

--↓ Term of a fibrant type.
--↓ This is just a term of the underlying extensional type.

_⊢ᶠ_ : (Γ : Type ℓ) (A : Γ ⊢ᶠType ℓ') → Type (ℓ ⊔ ℓ')
Γ ⊢ᶠ A = Γ ⊢ˣ ∣ A ∣

--↓ Context extension by a fibrant type.
--↓ This is just extension by the underlying extensional type.

_▷ᶠ_ : (Γ : Type ℓ) (A : Γ ⊢ᶠType ℓ') → Type (ℓ ⊔ ℓ')
Γ ▷ᶠ A = Γ ▷ˣ ∣ A ∣

------------------------------------------------------------------------------------------
-- Reindexing fibration structures and fibrations
------------------------------------------------------------------------------------------

--↓ Reindexing of fibration structures.

_∘ᶠˢ_ : {A : Γ → Type ℓ} (α : FibStr A) (ρ : Δ → Γ) → FibStr (A ∘ ρ)
(α ∘ᶠˢ ρ) .lift S γ r = α .lift S (ρ ∘ γ) r
(α ∘ᶠˢ ρ) .vary S T σ γ r = α .vary S T σ (ρ ∘ γ) r

--↓ Reindexing of fibrations.

_∘ᶠ_ : (Γ ⊢ᶠType ℓ) → (Δ → Γ) → Δ ⊢ᶠType ℓ
(A ∘ᶠ ρ) .fst = A .fst ∘ ρ
(A ∘ᶠ ρ) .snd = (A .snd) ∘ᶠˢ ρ

--↓ Restriction of a fibration structure or fibration along a cofibration.

_↾ᶠˢ_ : {A : Γ → Type ℓ} (α : FibStr A) (φ : Γ → Cof) → FibStr (A ↾ φ)
(α ↾ᶠˢ φ) = α ∘ᶠˢ 𝒑

_↾ᶠ_ : (A : Γ ⊢ᶠType ℓ) (φ : Γ → Cof) → Γ ▷[ φ ] ⊢ᶠType ℓ
(A ↾ᶠ φ) = A ∘ᶠ 𝒑

--↓ Reindexing fibration structures commutes with substitution.

opaque
  reindexSubst : {A A' : Γ → Type ℓ}
    (α : FibStr A) (P : A ≡ A') (ρ : Δ → Γ) (Q : A ∘ ρ ≡ A' ∘ ρ)
    → subst FibStr P α ∘ᶠˢ ρ ≡ subst FibStr Q (α ∘ᶠˢ ρ)
  reindexSubst α refl ρ refl = refl

------------------------------------------------------------------------------------------
-- Mapping boxes and fillers.
------------------------------------------------------------------------------------------

mapBox : {S : Shape} {r : ⟨ S ⟩}
  {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
  → (∀ {s} → A s → B s)
  → OpenBox S A r → OpenBox S B r
mapBox f box .cof = box .cof
mapBox f box .tube i u = f (box .tube i u)
mapBox f box .cap .out = f (box .cap .out)
mapBox f box .cap .out≡ u = cong f (box .cap .out≡ u)

mapFiller : {S : Shape} {r : ⟨ S ⟩}
  {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
  (f : ∀ {s} → A s → B s)
  {box : OpenBox S A r}
  → Filler box → Filler (mapBox f box)
mapFiller f filler .fill s = mapRestrict f (filler .fill s)
mapFiller f filler .cap≡ = cong f (filler .cap≡)

------------------------------------------------------------------------------------------
-- Extensionality principles.
------------------------------------------------------------------------------------------

opaque
  boxExt : {S : Shape} {A : ⟨ S ⟩ → Type ℓ} {r : ⟨ S ⟩}
    {box₀ box₁ : OpenBox S A r}
    → box₀ .cof ≡ box₁ .cof
    → (∀ i u v → box₀ .tube i u ≡ box₁ .tube i v)
    → box₀ .cap .out ≡ box₁ .cap .out
    → box₀ ≡ box₁
  boxExt {box₀ = box₀} refl q refl =
    congΣ (λ t c → makeBox (box₀ .cof) t (makeRestrict (box₀ .cap .out) c))
      (funExt' $ funExt' $ q _ _ _)
      (funExt' uip')

opaque
  boxExtDep : {S : Shape} {B : Type ℓ} {A : B → ⟨ S ⟩ → Type ℓ'}
    {b₀ b₁ : B} (b : b₀ ≡ b₁)
    {r : ⟨ S ⟩}
    {box₀ : OpenBox S (A b₀) r} {box₁ : OpenBox S (A b₁) r}
    → box₀ .cof ≡ box₁ .cof
    → (∀ i u v → subst (λ b' → A b' i) b (box₀ .tube i u) ≡ box₁ .tube i v)
    → subst (A ⦅–⦆ r) b (box₀ .cap .out) ≡ box₁ .cap .out
    → subst (OpenBox S ⦅–⦆ r ∘ A) b box₀ ≡ box₁
  boxExtDep refl = boxExt

opaque
  fillerExt : {S : Shape} {A : ⟨ S ⟩ → Type ℓ}  {r : ⟨ S ⟩}
    {box : OpenBox S A r}
    {f₀ f₁ : Filler box}
    → (∀ s → f₀ .fill s .out ≡ f₁ .fill s .out)
    → f₀ ≡ f₁
  fillerExt p =
    congΣ makeFiller (funExt $ restrictExt ∘ p) uip'

opaque
  FibStrExt : {A : Γ → Type ℓ} {α₀ α₁ : FibStr A}
    → (∀ S γ r box s → α₀ .lift S γ r box .fill s .out ≡ α₁ .lift S γ r box .fill s .out)
    → α₀ ≡ α₁
  FibStrExt q =
    congΣ makeFib
      (funExt' $ funExt' $ funExt' $ funExt' $ fillerExt $ q _ _ _ _)
      (funExt' $ funExt' $ funExt' $ funExt' $ funExt' $ funExt' $ funExt' uip')

------------------------------------------------------------------------------------------
-- Filling boxes expressed as partial elements in fibrations.
------------------------------------------------------------------------------------------

fibLiftPartial : (A : Γ ⊢ᶠType ℓ')
  (S : Shape) (γ : Γ ^ S) (r : ⟨ S ⟩) (φ : Cof)
  (part : (s : ⟨ S ⟩) → [ φ ∨ S ∋ r ≈ s ] → A $ᶠ γ s)
  → (s : ⟨ S ⟩) → A $ᶠ γ s [ φ ∨ S ∋ r ≈ s ↦ part s ]
fibLiftPartial (_ , α) S γ r φ part s .out =
  α .lift S γ r (partialToBox φ part) .fill s .out
fibLiftPartial (_ , α) S γ r φ part s .out≡ =
  ∨-elimEq
    (α .lift S γ r (partialToBox φ part) .fill s .out≡)
    (λ {refl → sym (α .lift S γ r (partialToBox φ part) .cap≡)})

fibVaryPartial : ∀ (A : Γ ⊢ᶠType ℓ')
  {S T} (σ : Shape[ S , T ]) (γ : Γ ^ T) (r : ⟨ S ⟩) (φ : Cof)
  (part : (t : ⟨ T ⟩) → [ φ ∨ T ∋ ⟪ σ ⟫ r ≈ t ] → A $ᶠ γ t)
  (s : ⟨ S ⟩)
  → fibLiftPartial A T γ (⟪ σ ⟫ r) φ part (⟪ σ ⟫ s) .out
    ≡ fibLiftPartial A S (γ ∘ ⟪ σ ⟫) r φ (reshapePartial σ part) s .out
fibVaryPartial (_ , α) σ γ r φ part s =
  α .vary _ _ σ γ r (partialToBox φ part) s
  ∙ cong
    (λ box' → α .lift _ (γ ∘ ⟪ σ ⟫) r box' .fill s .out)
    (boxExt refl (λ _ _ _ → cong (part _) (cofIsStrictProp' (_ ∨ _))) refl)

------------------------------------------------------------------------------------------
-- A strict retract of a fibration is a fibration.
------------------------------------------------------------------------------------------

Retractˣ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
Retractˣ A B γ = Retract (A γ) (B γ)

opaque
  retractFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    → Γ ⊢ˣ Retractˣ A B → FibStr B → FibStr A
  retractFibStr retract β .lift S γ r box = filler
    where
    fillerB : Filler (mapBox (retract _ .sec) box)
    fillerB = β .lift S γ r (mapBox (retract _ .sec) box)

    filler : Filler box
    filler .fill s .out = retract (γ s) .ret (fillerB .fill s .out)
    filler .fill s .out≡ u =
      sym (retract (γ s) .inv _)
      ∙ cong (retract (γ s) .ret) (fillerB .fill s .out≡ u)
    filler .cap≡ =
      cong (retract (γ r) .ret) (fillerB .cap≡)
      ∙ retract (γ r) .inv _

  retractFibStr retract β .vary S T σ γ r box s =
    cong (retract _ .ret) (β .vary S T σ γ r (mapBox (retract _ .sec) box) s)

opaque
  unfolding retractFibStr
  reindexRetractFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    (retract : Γ ⊢ˣ Retractˣ A B) {β : FibStr B} (ρ : Δ → Γ)
    → retractFibStr retract β ∘ᶠˢ ρ  ≡ retractFibStr (retract ∘ ρ) (β ∘ᶠˢ ρ)
  reindexRetractFibStr retract ρ = FibStrExt λ _ _ _ _ _ → refl

------------------------------------------------------------------------------------------
-- Corollary: fibration structures can be transferred across isomorphisms.
------------------------------------------------------------------------------------------

opaque
  isomorphFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    → Γ ⊢ˣ A ≅ˣ B → FibStr B → FibStr A
  isomorphFibStr iso β = retractFibStr (isoToRetract ∘ iso) β

opaque
  unfolding isomorphFibStr
  reindexIsomorphFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    (iso : Γ ⊢ˣ A ≅ˣ B) {β : FibStr B} (ρ : Δ → Γ)
    → isomorphFibStr iso β ∘ᶠˢ ρ ≡ isomorphFibStr (iso ∘ ρ) (β ∘ᶠˢ ρ)
  reindexIsomorphFibStr _ = reindexRetractFibStr _
