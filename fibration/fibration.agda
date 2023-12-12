{-

Defines fibration structures and fibrations.

-}
module fibration.fibration where

open import prelude
open import axiom
open import cofibration

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

infix  1 _⊢ᶠType_ _⊢ᶠ_
infixl 3 _▷ᶠ_
infixl 5 _∘ᶠˢ_ _∘ᶠ_

------------------------------------------------------------------------------------------
-- Open boxes
------------------------------------------------------------------------------------------

record OpenBox (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ → Type ℓ) : Type ℓ
  where
  constructor makeBox
  field
    cof : Cof
    tube : (i : ⟨ S ⟩) → [ cof ] → A i
    cap : A r [ cof ↦ tube r ]

open OpenBox public

reshapeBox : ∀ {S T} (σ : ShapeHom S T) {r} {A : ⟨ T ⟩ → Type ℓ}
  → OpenBox T (⟪ σ ⟫ r) A → OpenBox S r (A ∘ ⟪ σ ⟫)
reshapeBox σ box .cof = box .cof
reshapeBox σ box .tube = box .tube ∘ ⟪ σ ⟫
reshapeBox σ box .cap = box .cap

mapBox : {S : Shape} {r : ⟨ S ⟩}
  {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
  → (∀ s → A s → B s)
  → OpenBox S r A → OpenBox S r B
mapBox f box .cof = box .cof
mapBox f box .tube i u = f i (box .tube i u)
mapBox f box .cap .out = f _ (box .cap .out)
mapBox f box .cap .out≡ u = cong (f _) (box .cap .out≡ u)

addToTube : ∀ {S r} {A : ⟨ S ⟩ → Type ℓ}
  (box : OpenBox S r A)
  (φ : Cof)
  (t : (i : ⟨ S ⟩) → [ φ ] → A i [ box .cof ↦ box .tube i ])
  (matchCap : (v : [ φ ]) → t r v .out ≡ box .cap .out)
  → OpenBox S r A
addToTube box φ t matchCap .cof = box .cof ∨ φ
addToTube box φ t matchCap .tube i =
  ∨-rec (box .cof) φ (box .tube i) (out ∘ t i) (λ u v → t i v .out≡ u)
addToTube box φ t matchCap .cap .out = box .cap .out
addToTube box φ t matchCap .cap .out≡ =
  ∨-elimEq (box .cof) φ (box .cap .out≡) matchCap

boxToPartial : ∀ {S r} {A : ⟨ S ⟩ → Type ℓ} (box : OpenBox S r A)
  (s : ⟨ S ⟩) → [ box .cof ∨ S ∋ r ≈ s ] → A s
boxToPartial {S = S} {r} box s =
  ∨-rec (box .cof) (S ∋ r ≈ s)
    (box .tube s)
    (λ {refl → box .cap .out})
    (λ {u refl → box .cap .out≡ u})

opaque
  varyBoxToPartial : ∀ {S T} (σ : ShapeHom S T) {r} {A : ⟨ T ⟩ → Type ℓ}
    (box : OpenBox T (⟪ σ ⟫ r) A)
    (s : ⟨ S ⟩)
    (v : [ box .cof ∨ T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s ])
    (u : [ box .cof ∨ S ∋ r ≈ s ])
    → boxToPartial box (⟪ σ ⟫ s) v ≡ boxToPartial (reshapeBox σ box) s u
  varyBoxToPartial {S = S} {T} σ {r} box s =
    takeOutCof (box .cof) (T ∋ ⟪ σ ⟫ r ≈ ⟪ σ ⟫ s)(S ∋ r ≈ s)
      (λ u → refl)
      (λ {refl refl → refl})

opaque
  boxExt : {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ}
    {box box' : OpenBox S r A}
    → box .cof ≡ box' .cof
    → (∀ i u v → box .tube i u ≡ box' .tube i v)
    → box .cap .out ≡ box' .cap .out
    → box ≡ box'
  boxExt {box = box} refl q refl =
    congΣ (λ t c → makeBox (box .cof) t (makeRestrict (box .cap .out) c))
      (funExt' $ funExt' $ q _ _ _)
      (funExt' uip')

opaque
  boxExtDep : {S : Shape} {B : Type ℓ} {A : B → ⟨ S ⟩ → Type ℓ'}
    {b₀ b₁ : B} (b : b₀ ≡ b₁)
    {r : ⟨ S ⟩}
    {box₀ : OpenBox S r (A b₀)} {box₁ : OpenBox S r (A b₁)}
    → box₀ .cof ≡ box₁ .cof
    → (∀ i u v → subst (λ b' → A b' i) b (box₀ .tube i u) ≡ box₁ .tube i v)
    → subst (A ⦅–⦆ r) b (box₀ .cap .out) ≡ box₁ .cap .out
    → subst (OpenBox S r ∘ A) b box₀ ≡ box₁
  boxExtDep refl f r x = boxExt f r x

------------------------------------------------------------------------------------------
-- Solutions to individual lifting problems
------------------------------------------------------------------------------------------

record Filler {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ} (box : OpenBox S r A) : Type ℓ
  where
  constructor makeFiller
  field
    fill : (s : ⟨ S ⟩) → A s [ box .cof ↦ box .tube s ]
    cap≡ : fill r .out ≡ box .cap .out

open Filler public

reshapeFiller : {S T : Shape} (σ : ShapeHom S T)
  {r : ⟨ S ⟩} {A : ⟨ T ⟩ → Type ℓ}
  {box : OpenBox T (⟪ σ ⟫ r) A}
  → Filler box
  → Filler (reshapeBox σ box)
reshapeFiller σ w .fill = w .fill ∘ ⟪ σ ⟫
reshapeFiller σ w .cap≡ = w .cap≡

opaque
  fillerExt : {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ}
    {box : OpenBox S r A}
    {co co' : Filler box}
    → (∀ s → co .fill s .out ≡ co' .fill s .out)
    → co ≡ co'
  fillerExt p =
    congΣ makeFiller (funExt $ restrictExt ∘ p) uip'

opaque
  fillerCong : {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ}
    {box : OpenBox S r A}
    {co co' : Filler box}
    → co ≡ co'
    → (∀ s → co .fill s .out ≡ co' .fill s .out)
  fillerCong p s = cong out (appCong (cong fill p))

fitsPartialToFiller : ∀ {S r} {A : ⟨ S ⟩ → Type ℓ} {box : OpenBox S r A}
  → ((s : ⟨ S ⟩) → A s [ box .cof ∨ S ∋ r ≈ s ↦ boxToPartial box s ])
  → Filler box
fitsPartialToFiller filler .fill s = narrow (filler s) ∨l
fitsPartialToFiller filler .cap≡ = sym (filler _ .out≡ (∨r refl))

------------------------------------------------------------------------------------------
-- Equivariant fibrations
------------------------------------------------------------------------------------------

record FibStr {Γ : Type ℓ} (A : Γ → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor makeFib
  field
    lift : ∀ S r p (box : OpenBox S r (A ∘ p)) → Filler box
    vary : ∀ S T (σ : ShapeHom S T) r p box s
      → reshapeFiller σ (lift T (⟪ σ ⟫ r) p box) .fill s .out
        ≡ lift S r (p ∘ ⟪ σ ⟫) (reshapeBox σ box) .fill s .out

open FibStr public

_⊢ᶠType_ : (Γ : Type ℓ) (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Γ ⊢ᶠType ℓ' = Σ (Γ → Type ℓ') FibStr

_⊢ᶠ_ : (Γ : Type ℓ) (A : Γ ⊢ᶠType ℓ') → Type (ℓ ⊔ ℓ')
Γ ⊢ᶠ A = Γ ⊢ A .fst

_▷ᶠ_ : (Γ : Type ℓ) (A : Γ ⊢ᶠType ℓ') → Type (ℓ ⊔ ℓ')
Γ ▷ᶠ A = Γ ▷ A .fst

------------------------------------------------------------------------------------------
-- Reindexing fibration structures and fibrations
------------------------------------------------------------------------------------------

_∘ᶠˢ_ : {A : Γ → Type ℓ} (α : FibStr A) (ρ : Δ → Γ) → FibStr (A ∘ ρ)
(α ∘ᶠˢ ρ) .lift S r p = α .lift S r (ρ ∘ p)
(α ∘ᶠˢ ρ) .vary S T σ r p = α .vary S T σ r (ρ ∘ p)

_∘ᶠ_ : (Γ ⊢ᶠType ℓ) → (Δ → Γ) → Δ ⊢ᶠType ℓ
(A ∘ᶠ ρ) .fst = A .fst ∘ ρ
(A ∘ᶠ ρ) .snd = (A .snd) ∘ᶠˢ ρ

opaque
  reindexSubst : {A A' : Γ → Type ℓ}
    (α : FibStr A) (P : A ≡ A') (ρ : Δ → Γ) (Q : A ∘ ρ ≡ A' ∘ ρ)
    → subst FibStr P α ∘ᶠˢ ρ ≡ subst FibStr Q (α ∘ᶠˢ ρ)
  reindexSubst α refl ρ refl = refl

------------------------------------------------------------------------------------------
-- Extensionality principles for fibrations
------------------------------------------------------------------------------------------

FibStrEq : {Γ : Type ℓ} {A : Γ → Type ℓ'} (α₀ α₁ : FibStr A) → Type (ℓ ⊔ ℓ')
FibStrEq {Γ = Γ} {A = A} α₀ α₁ =
  ((S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → Γ)
  (box : OpenBox S r (A ∘ p))
  (s : ⟨ S ⟩) → α₀ .lift S r p box .fill s .out ≡ α₁ .lift S r p box .fill s .out)

opaque
  FibStrExt : {A : Γ → Type ℓ} {α α' : FibStr A} → FibStrEq α α' → α ≡ α'
  FibStrExt q =
    congΣ makeFib
      (funExt' $ funExt' $ funExt' $ funExt' $ fillerExt $ q _ _ _ _)
      (funExt' $ funExt' $ funExt' $ funExt' $ funExt' $ funExt' $ funExt' uip')

------------------------------------------------------------------------------------------
-- A retract of a fibration is a fibration
------------------------------------------------------------------------------------------

Retractᴵ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
Retractᴵ A B γ = Retract (A γ) (B γ)

opaque
  retractFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    → Γ ⊢ Retractᴵ A B → FibStr B → FibStr A
  retractFibStr retract β .lift S r p box = filler
    where
    fillerB : Filler (mapBox (sec ∘ retract ∘ p) box)
    fillerB = β .lift S r p (mapBox (sec ∘ retract ∘ p) box)

    filler : Filler box
    filler .fill s .out = retract (p s) .ret (fillerB .fill s .out)
    filler .fill s .out≡ u =
      sym (appCong (retract (p s) .inv))
      ∙ cong (retract (p s) .ret) (fillerB .fill s .out≡ u)
    filler .cap≡ =
      cong (retract (p r) .ret) (fillerB .cap≡)
      ∙ appCong (retract (p r) .inv)

  retractFibStr retract β .vary S T σ r p box s =
    cong (retract _ .ret) (β .vary S T σ r p (mapBox (sec ∘ retract ∘ p) box) s)

opaque
  unfolding retractFibStr
  reindexRetractFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    (retract : Γ ⊢ Retractᴵ A B) {β : FibStr B} (ρ : Δ → Γ)
    → retractFibStr retract β ∘ᶠˢ ρ  ≡ retractFibStr (retract ∘ ρ) (β ∘ᶠˢ ρ)
  reindexRetractFibStr retract ρ = FibStrExt λ _ _ _ _ _ → refl

------------------------------------------------------------------------------------------
-- Corollary: fibration structures can be transferred across isomorphisms
------------------------------------------------------------------------------------------

_≅ᴵ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → (Γ → Type (ℓ ⊔ ℓ'))
_≅ᴵ_ A B γ = A γ ≅ B γ

opaque
  isomorphFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    → Γ ⊢ A ≅ᴵ B → FibStr B → FibStr A
  isomorphFibStr iso β = retractFibStr (isoToRetract ∘ iso) β

opaque
  unfolding isomorphFibStr
  reindexIsomorphFibStr : {A : Γ → Type ℓ} {B : Γ → Type ℓ'}
    (iso : Γ ⊢ A ≅ᴵ B) {β : FibStr B} (ρ : Δ → Γ)
    → isomorphFibStr iso β ∘ᶠˢ ρ ≡ isomorphFibStr (iso ∘ ρ) (β ∘ᶠˢ ρ)
  reindexIsomorphFibStr _ = reindexRetractFibStr _
